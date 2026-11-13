import HarmonicBalls.FirstPass.Phase2.ForallXiStep8Derived
import LatticeProb.Bonanno.LQGMetric.Statement.Dimension

/-!
# The Step 8 identification for every Weyl exponent from the canonical one

`IsLQGMetric γ ξ 𝔇` (`Defs/LQGMetric.lean`) takes the Weyl exponent `ξ` as a parameter, while a γ-LQG metric exists only
for `ξ = γ / d_γ` (Dubédat-Falconet-Gwynne-Pfeffer-Sun, arXiv:1905.00380, Theorem 1.5, p. 7: the scaling constants of a
weak LQG metric satisfy `c_{δr} / c_r = δ^{ξ Q + o(1)}`, which pins `Q = 2/γ + γ/2` and hence `γ`; Ding-Gwynne,
arXiv:1807.01072, for the range of `γ ↦ γ / d_γ`). Every clause of `Step8IdentificationStmt` that involves a model has a
premise `IsLQGMetricOfField P γ ξ α hC D`, which unfolds to the existence of some `𝔇` with `IsLQGMetric γ ξ 𝔇`. Hence:

* `step8Identification_of_canonical_of_weylExponentEq`: if every γ-LQG metric has the canonical Weyl exponent
  `lqgXi γ`, then `Step8IdentificationStmt` (every `ξ`) follows from `Step8IdentificationCanonicalStmt` (`ξ = lqgXi γ`):
  at `ξ = lqgXi γ` the two statements coincide, and at any other `ξ` the event `E = univ` and `q = 0` satisfy every clause
  vacuously.
* `weylExponentEq_lqgXi_of_xiGamma`: the hypothesis in the canonical normalization of the paper, from its two parts: the
  Weyl exponent is Gwynne-Miller's `LQGMetric.xiGamma γ = γ / LQGMetric.dGamma γ`, and the paper's `lqgXi γ` equals it
  (the identification of the dimension `d_γ`, Ding-Gwynne, arXiv:1807.01072, Theorem 1.4).
* `correctedLemma11_13_of_canonicalStep8`, `firstPass_11_11_of_canonicalStep8`, `firstPass_1_2_of_canonicalStep8`:
  Lemma 11.13 (corrected), Proposition 11.11 and Theorem 1.2 for every `ξ` from the canonical Step 8 identification and
  the two parts of the Weyl exponent identification.

The statements of the draft are unchanged; the proofs are applications.
-/

universe u

namespace HarmonicBalls

open MeasureTheory

/-- **Step 8 identification for every `ξ` from the canonical one.** If every γ-LQG metric (`0 < γ < 2`) has Weyl
exponent `lqgXi γ`, then `Step8IdentificationStmt` follows from `Step8IdentificationCanonicalStmt`. At `ξ ≠ lqgXi γ` no
model carries an LQG metric of exponent `ξ`, so `E = univ` and `q = 0` satisfy every clause. -/
theorem step8Identification_of_canonical_of_weylExponentEq
    (hξ : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 → ξ = lqgXi γ)
    (hCan : Step8IdentificationCanonicalStmt.{u}) : Step8IdentificationStmt.{u} := by
  intro U V W T Q' Q δ₀ hgeom γ ξ α₀ M hγ0 hγ2 hα hM
  by_cases hcan : ξ = lqgXi γ
  · subst hcan
    exact hCan U V W T Q' Q δ₀ hgeom γ α₀ M hγ0 hγ2 hα hM
  · have hno : ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (α : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
        (D : Ω → ℂ → ℂ → ℝ), ¬ IsLQGMetricOfField P γ ξ α hC D := by
      rintro Ω _ P α hC D ⟨𝔇, h𝔇, -⟩
      exact hcan (hξ γ ξ hγ0 hγ2 𝔇 h𝔇)
    refine ⟨Set.univ, ⟨MeasurableSet.univ, ?_⟩, 0, ?_, ?_⟩
    · intro Ω _ P hC _ _ D _ _ hD
      exact (hno P γ hC D hD).elim
    · intro Ω _ P hC _ _ D _ _ hD
      exact (hno P γ hC D hD).elim
    · intro Ω _ P hC _ _ D _ _ hD
      exact (hno P α₀ hC D hD).elim

/-- **The Weyl exponent in the paper's normalization.** If every γ-LQG metric has Gwynne-Miller's Weyl exponent
`LQGMetric.xiGamma γ` and the paper's canonical exponent `lqgXi γ` equals it, then every γ-LQG metric has Weyl exponent
`lqgXi γ`. -/
theorem weylExponentEq_lqgXi_of_xiGamma
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDim : ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ) :
    ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 → ξ = lqgXi γ :=
  fun γ ξ hγ0 hγ2 𝔇 h𝔇 => (hXi γ ξ hγ0 hγ2 𝔇 h𝔇).trans (hDim γ hγ0 hγ2).symm

/-- **Lemma 11.13 (corrected, every `ξ`)** from the canonical Step 8 identification `hCan`, the Weyl exponent of every
γ-LQG metric `hXi`, and the identification `hDim` of the paper's canonical exponent with Gwynne-Miller's. -/
theorem correctedLemma11_13_of_canonicalStep8
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDim : ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ)
    (hCan : Step8IdentificationCanonicalStmt.{u}) : CorrectedLemma11_13Stmt.{u} :=
  correctedLemma11_13_derivedStep8
    (step8Identification_of_canonical_of_weylExponentEq (weylExponentEq_lqgXi_of_xiGamma hXi hDim) hCan)

/-- **Proposition 11.11 (every `ξ`)** from the canonical Step 8 identification and the Weyl exponent identification. -/
theorem firstPass_11_11_of_canonicalStep8
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDim : ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ)
    (hCan : Step8IdentificationCanonicalStmt.{u}) : HarmonicBallNotMetricBallStmt.{u} :=
  firstPass_11_11_derivedStep8
    (step8Identification_of_canonical_of_weylExponentEq (weylExponentEq_lqgXi_of_xiGamma hXi hDim) hCan)

/-- **Theorem 1.2 (every `ξ`)** from the canonical Step 8 identification and the Weyl exponent identification. -/
theorem firstPass_1_2_of_canonicalStep8
    (hXi : ∀ γ ξ : ℝ, 0 < γ → γ < 2 → ∀ 𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ, IsLQGMetric γ ξ 𝔇 →
      ξ = LQGMetric.xiGamma γ)
    (hDim : ∀ γ : ℝ, 0 < γ → γ < 2 → lqgXi γ = LQGMetric.xiGamma γ)
    (hCan : Step8IdentificationCanonicalStmt.{u}) : HarmonicBallNoveltyStmt.{u} :=
  firstPass_1_2_derivedStep8
    (step8Identification_of_canonical_of_weylExponentEq (weylExponentEq_lqgXi_of_xiGamma hXi hDim) hCan)

end HarmonicBalls
