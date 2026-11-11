import HarmonicBalls.FirstPass.Frozen.S11n
import HarmonicBalls.FirstPass.S11i.Faithful

/-!
# Canonical-exponent form of the frozen canonical decoder existence

`LQGCanonicalDecodersExistStmt` (`FirstPass/Frozen/S11n.lean:33`) and its measurable strengthening
`LQGCanonicalDecodersMeasurableExistStmt` (`FirstPass/Frozen/S11n.lean:71`) quantify over a free exponent `ξ`.
Gwynne-Miller, Theorem 1.2, does not justify the free `ξ`, and allows the narrowing of each existence statement to the canonical
exponent `lqgXi γ = γ / d_γ` (`FirstPass/S11i/Faithful.lean:94`). The frozen statements are kept unchanged. The forms
below are the narrowed statements; `_of_free` shows that each is a consequence of its frozen form.
-/

namespace HarmonicBalls

open MeasureTheory

universe u

/-- Canonical-exponent form of `LQGCanonicalDecodersExistStmt`: the identification clause is required only for the
canonical exponent `lqgXi γ` (the free `ξ` of the frozen statement is replaced by `lqgXi γ` in every place). -/
def LQGCanonicalDecodersExistCanonXiStmt : Prop :=
  ∀ (γ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∃ (Dμ : S11n.CanonSpace → Measure ℂ) (Dd : S11n.CanonSpace → ℂ → ℂ → ℝ),
      S11n.LQGCanonicalIdentificationStmt.{u} γ (lqgXi γ) α₀ Dμ Dd

/-- Canonical-exponent form of `LQGCanonicalDecodersMeasurableExistStmt` (the same clauses 1-4 with `ξ := lqgXi γ`). -/
def LQGCanonicalDecodersMeasurableExistCanonXiStmt : Prop :=
  ∀ (γ α₀ : ℝ), 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∃ (K : ProbabilityTheory.Kernel S11n.CanonSpace ℂ) (d : S11n.CanonSpace → ContinuousMap (ℂ × ℂ) ℝ),
      ProbabilityTheory.IsSFiniteKernel K ∧ (∀ L, MeasureTheory.IsFiniteMeasureOnCompacts (K L)) ∧
      Measurable d ∧
      S11n.LQGCanonicalIdentificationStmt.{u} γ (lqgXi γ) α₀ (fun L => K L) (fun L x y => d L (x, y)) ∧
      ∃ G : Set S11n.CanonSpace, MeasurableSet G ∧
        (∀ (Ω : Type u) [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω) (hC : Ω → (ℂ → ℝ) → ℝ)
          (hcirc : Ω → ℝ → ℂ → ℝ),
          IsWholePlaneGFF P hC hcirc → ∀ᵐ ω ∂P, alphaCanon α₀ hC ω ∈ G) ∧
        ∀ L ∈ G, (K L).support = Set.univ ∧ IsEuclideanLengthMetric (fun x y => d L (x, y))

/-- The canonical-exponent form follows from the frozen free-`ξ` form (instantiate `ξ := lqgXi γ`). -/
theorem lqgCanonicalDecodersExistCanonXi_of_free (h : LQGCanonicalDecodersExistStmt.{u}) :
    LQGCanonicalDecodersExistCanonXiStmt.{u} :=
  fun γ α₀ hγ0 hγ2 hα => h γ (lqgXi γ) α₀ hγ0 hγ2 hα

/-- The measurable canonical-exponent form follows from the frozen measurable free-`ξ` form. -/
theorem lqgCanonicalDecodersMeasurableExistCanonXi_of_free (h : LQGCanonicalDecodersMeasurableExistStmt.{u}) :
    LQGCanonicalDecodersMeasurableExistCanonXiStmt.{u} :=
  fun γ α₀ hγ0 hγ2 hα => h γ (lqgXi γ) α₀ hγ0 hγ2 hα

/-- The weak canonical-exponent form is the projection of the measurable canonical-exponent form (as
`lqgCanonicalDecodersExist_of_measurable`, `FirstPass/S11i/Final11_13.lean:150`, in the free-`ξ` case). -/
theorem lqgCanonicalDecodersExistCanonXi_of_measurableCanonXi (h : LQGCanonicalDecodersMeasurableExistCanonXiStmt.{u}) :
    LQGCanonicalDecodersExistCanonXiStmt.{u} := by
  intro γ α₀ h0 h1 h2
  obtain ⟨K, d, -, -, -, hId, -⟩ := h γ α₀ h0 h1 h2
  exact ⟨fun L => K L, fun L x y => d L (x, y), hId⟩

end HarmonicBalls
