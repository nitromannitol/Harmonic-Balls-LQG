import HarmonicBalls.FirstPass.S11i.Faithful
import HarmonicBalls.FirstPass.S11i.AlphaCanonical

/-!
# Restoring the arbitrary model in Lemma 11.13 (Step 15 of `notes/fp-gaps/CHATGPT-11-13-proof.md`, first pass fp-S11n)

Birkhoff is applied on the canonical field space (mean-zero pairings `CanonSpace`, the canonical field `alphaCanon`),
not on the arbitrary probability space of the Draft. This file is the pull-back from that canonical statement to an
arbitrary whole-plane GFF model `(Ω, P, hC, hcirc)` with LQG measure `μ` and LQG metric `D`.

Interface for the assembly of `firstPass_11_13_corrected` (owner n3):

* `CanonicalPinchConullStmt α₀ M δ U T Q' Q Dμ Dd` (input, proved by the canonical Birkhoff argument): a measurable set
  `G` of canonical fields such that, for every whole-plane GFF model, the canonical field of `h^{α₀}` lies in `G` almost
  surely, and for every `L ∈ G` and `Dμ L`-almost every `z`, the eventual frequency bound holds along
  `pinchPointEvent (Dμ L) (Dd L)`.
* `LQGCanonicalIdentificationStmt γ ξ α₀ Dμ Dd` (NAMED INPUT, not frozen; see the report): almost surely the LQG measure
  and the LQG metric of the model are positive multiples of the canonical decoders `Dμ` and `Dd` at the canonical field.
* `correctedLemma11_13_of_canonical`: from these two inputs, the body of `CorrectedLemma11_13Stmt`
  (`HarmonicBalls/FirstPass/S11i/Faithful.lean:72`) with the density `δ` chosen before the probability space.

Positive rescalings are harmless: `pinchPointEvent` is invariant under `μ ↦ a • μ` and `D ↦ b • D` for `a, b > 0`
(`pinchPointEvent_smul_iff`), since the annulus Green potential is linear in the measure and the distances are
positively homogeneous.
-/

universe u

namespace HarmonicBalls.S11n

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal Pointwise

/-- The canonical field space of Lemma 11.13: pairings with mean-zero test functions on `ℂ`
(`ModConstTestPairings`, the field `h^α` modulo additive constants). -/
abbrev CanonSpace : Type := ModConstTestPairings (Set.univ : Set ℂ)

/-- Canonical conull statement (input of the pull-back; the Birkhoff argument of write-up Steps 9-14 on the canonical
field space). For the sets `U T Q' Q`, the insertion `α₀`, the parameter `M` and the density `δ`, and given canonical
decoders `Dμ` (measures) and `Dd` (metrics): there is a measurable set `G` of canonical fields such that

* for every whole-plane GFF model `(Ω, P, hC, hcirc)`, the canonical field `alphaCanon α₀ hC ω` lies in `G` for almost
  every `ω` (the canonical law is model-independent, `canonicalLaw_eq_of_isWholePlaneGFF`, `CanonicalLawUniversal.lean`);
* for every `L ∈ G`, `Dμ L`-almost every `z` satisfies the eventual frequency bound
  `δ N ≤ #{n ∈ [N+1, 2N] : pinchPointEvent (Dμ L) (Dd L) U T Q' Q M (2⁻¹)^n z}`. -/
def CanonicalPinchConullStmt (α₀ M δ : ℝ) (U T Q' Q : Set ℂ) (Dμ : CanonSpace → Measure ℂ)
    (Dd : CanonSpace → ℂ → ℂ → ℝ) : Prop :=
  ∃ G : Set CanonSpace, MeasurableSet G ∧
    (∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → ∀ᵐ ω ∂P, alphaCanon α₀ hC ω ∈ G) ∧
    ∀ L ∈ G, ∀ᵐ z ∂(Dμ L), ∀ᶠ N in atTop,
      δ * N ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ pinchPointEvent (Dμ L) (Dd L) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard :
        ℝ)

/-- NAMED INPUT (not frozen; operator source-check required). Identification of the LQG measure and the LQG metric of
a whole-plane GFF model with canonical decoders. For every model with `IsLQGMeasureOfField P γ α₀ hcirc μ` and
`IsLQGMetricOfField P γ ξ α₀ hC D`, almost surely there are constants `a, b > 0` with `μ ω = a • Dμ (canonical field)` and
`D ω = b • Dd (canonical field)`. The constants absorb the additive-constant normalisation of the field (`μ_{h+c} =
e^{γ c} μ_h`, `D_{h+c} = e^{ξ c} D_h`); `pinchPointEvent` is invariant under such rescalings. -/
def LQGCanonicalIdentificationStmt (γ ξ α₀ : ℝ) (Dμ : CanonSpace → Measure ℂ) (Dd : CanonSpace → ℂ → ℂ → ℝ) :
    Prop :=
  ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
    ∀ᵐ ω ∂P, ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ μ ω = ENNReal.ofReal a • Dμ (alphaCanon α₀ hC ω) ∧
      ∀ u v, D ω u v = b * Dd (alphaCanon α₀ hC ω) u v

/-- Positive homogeneity of the set distance `D(A, B) = inf_{x ∈ A, y ∈ B} D(x, y)` (`setDist`, `Defs/LQGMetric.lean`). -/
theorem setDist_smul_left {b : ℝ} (hb : 0 ≤ b) (d : ℂ → ℂ → ℝ) (A B : Set ℂ) :
    setDist (fun u v => b * d u v) A B = b * setDist d A B := by
  have h : image2 (fun u v => b * d u v) A B = b • image2 d A B := by
    ext t
    simp only [mem_image2, Set.mem_smul_set, smul_eq_mul]
    constructor
    · rintro ⟨x, hx, y, hy, rfl⟩
      exact ⟨d x y, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    · rintro ⟨s, ⟨x, hx, y, hy, rfl⟩, rfl⟩
      exact ⟨x, hx, y, hy, rfl⟩
  unfold setDist
  rw [h, Real.sInf_smul_of_nonneg hb, smul_eq_mul]

/-- The annulus Green potential is linear in the measure (`lintegral_smul_measure`). -/
theorem annulusGreenPotentialSup_smul (a : ℝ≥0∞) (ν : Measure ℂ) (x₀ : ℂ) (p q : ℝ) :
    annulusGreenPotentialSup (a • ν) x₀ p q = a * annulusGreenPotentialSup ν x₀ p q := by
  unfold annulusGreenPotentialSup
  simp only [Measure.restrict_smul, lintegral_smul_measure, ENNReal.mul_iSup, smul_eq_mul]

/-- `pinchPointEvent` is invariant under the rescalings `μ ↦ a • μ` and `D ↦ b • D` with `a, b > 0`. -/
theorem pinchPointEvent_smul_iff {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (ν : Measure ℂ) (d : ℂ → ℂ → ℝ)
    (U T Q' Q : Set ℂ) (M r : ℝ) (z : ℂ) :
    pinchPointEvent (ENNReal.ofReal a • ν) (fun u v => b * d u v) U T Q' Q M r z ↔
      pinchPointEvent ν d U T Q' Q M r z := by
  have hA : ENNReal.ofReal a ≠ 0 := (ENNReal.ofReal_pos.2 ha).ne'
  have hA' : ENNReal.ofReal a ≠ ⊤ := ENNReal.ofReal_ne_top
  have hB : ENNReal.ofReal b ≠ 0 := (ENNReal.ofReal_pos.2 hb).ne'
  have hB' : ENNReal.ofReal b ≠ ⊤ := ENNReal.ofReal_ne_top
  unfold pinchPointEvent
  simp only [setDist_smul_left hb.le, ENNReal.ofReal_mul hb.le, ← ENNReal.mul_iSup,
    annulusGreenPotentialSup_smul, Measure.smul_apply, smul_eq_mul]
  refine and_congr ?_ (and_congr ?_ ?_)
  · exact ENNReal.mul_lt_mul_iff_right hB hB'
  · exact ENNReal.mul_lt_mul_iff_right hB hB'
  · rw [mul_left_comm, ENNReal.mul_lt_mul_iff_right hA hA']

/-- Pull-back of the canonical conull statement to an arbitrary whole-plane GFF model (Step 15 of
`CHATGPT-11-13-proof.md`). The density `δ` does not depend on the model. -/
theorem restoreModel_11_13 {γ ξ α₀ M δ : ℝ} {U T Q' Q : Set ℂ} {Dμ : CanonSpace → Measure ℂ}
    {Dd : CanonSpace → ℂ → ℂ → ℝ}
    (hCan : CanonicalPinchConullStmt.{u} α₀ M δ U T Q' Q Dμ Dd)
    (hId : LQGCanonicalIdentificationStmt.{u} γ ξ α₀ Dμ Dd) :
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
      (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
      ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ᶠ N in atTop,
        δ * N ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard :
          ℝ) := by
  intro Ω _ P hC hcirc μ D hh hμ hD
  obtain ⟨G, -, hGuniv, hGgood⟩ := hCan
  filter_upwards [hGuniv Ω P hC hcirc hh, hId Ω P hC hcirc μ D hh hμ hD] with ω hωG hωI
  obtain ⟨a, b, ha, hb, hμω, hDω⟩ := hωI
  have hD' : D ω = fun u v => b * Dd (alphaCanon α₀ hC ω) u v := funext fun u => funext fun v => hDω u v
  rw [hμω, hD']
  have key : ∀ z : ℂ,
      (∀ᶠ N in atTop, δ * N ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEvent (ENNReal.ofReal a • Dμ (alphaCanon α₀ hC ω)) (fun u v => b * Dd (alphaCanon α₀ hC ω) u v)
          U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard : ℝ)) ↔
      ∀ᶠ N in atTop, δ * N ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧
        pinchPointEvent (Dμ (alphaCanon α₀ hC ω)) (Dd (alphaCanon α₀ hC ω)) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard :
          ℝ) := by
    intro z
    have hev : ∀ n : ℕ,
        pinchPointEvent (ENNReal.ofReal a • Dμ (alphaCanon α₀ hC ω)) (fun u v => b * Dd (alphaCanon α₀ hC ω) u v)
          U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z ↔
        pinchPointEvent (Dμ (alphaCanon α₀ hC ω)) (Dd (alphaCanon α₀ hC ω)) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z :=
      fun n => pinchPointEvent_smul_iff ha hb _ _ _ _ _ _ _ _ _
    simp only [hev]
  rw [Measure.ae_ennreal_smul_measure_iff (ENNReal.ofReal_pos.2 ha).ne']
  filter_upwards [hGgood _ hωG] with z hz
  exact (key z).2 hz

/-- The bridge to `CorrectedLemma11_13Stmt` (`HarmonicBalls/FirstPass/S11i/Faithful.lean:72`), body after the geometry
and the parameters `γ, α₀, ξ, M` are fixed: the canonical inputs give the density `δ ∈ (0,1)` chosen before the
probability space, and then the conclusion for every model. -/
theorem correctedLemma11_13_of_canonical {γ ξ α₀ M : ℝ} {U T Q' Q : Set ℂ}
    (h : ∃ δ ∈ Ioo (0 : ℝ) 1, ∃ (Dμ : CanonSpace → Measure ℂ) (Dd : CanonSpace → ℂ → ℂ → ℝ),
      CanonicalPinchConullStmt.{u} α₀ M δ U T Q' Q Dμ Dd ∧
        LQGCanonicalIdentificationStmt.{u} γ ξ α₀ Dμ Dd) :
    ∃ δ ∈ Ioo (0 : ℝ) 1, ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
      (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ) (D : Ω → ℂ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ → IsLQGMetricOfField P γ ξ α₀ hC D →
      ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ᶠ N in atTop,
        δ * N ≤ ({n : ℕ | N + 1 ≤ n ∧ n ≤ 2 * N ∧ pinchPointEvent (μ ω) (D ω) U T Q' Q M ((2 : ℝ)⁻¹ ^ n) z}.ncard :
          ℝ) := by
  obtain ⟨δ, hδ, Dμ, Dd, hCan, hId⟩ := h
  exact ⟨δ, hδ, fun Ω _ P hC hcirc μ D hh hμ hD => restoreModel_11_13 hCan hId Ω P hC hcirc μ D hh hμ hD⟩

end HarmonicBalls.S11n
