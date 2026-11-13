import HarmonicBalls.FirstPass.S11i.CanonicalLawUniversal
import HarmonicBalls.FirstPass.S11i.AlphaCanonical

/-!
# The law of the canonical field of `h - α log|·|` does not depend on the model

For a whole-plane GFF model `(Ω, P, hC, hcirc)` and `α : ℝ`, the canonical field `alphaCanon α hC ω`
(`S11i/AlphaCanonical.lean`) records the pairings of `h^α = h^ℂ - α log|·|` with mean-zero test functions. It is the
translate by the deterministic log drift `logDrift α` of the canonical field of `h^ℂ`, whose law on the canonical space
is the same for every model (`canonicalLaw_eq_of_isWholePlaneGFF`: the finite-dimensional laws of mean-zero pairings
are centred Gaussian with the covariance of the whole-plane GFF, and they generate the product σ-algebra). Hence:

* `measurable_alphaCanon`: `alphaCanon α hC` is measurable;
* `map_alphaCanon_eq_of_isWholePlaneGFF`: two models give the same law of `alphaCanon α ·`;
* `ae_alphaCanon_mem_of_isWholePlaneGFF`: a measurable set of canonical fields that contains the canonical field almost
  surely under one model contains it almost surely under every model.
-/

namespace HarmonicBalls

open MeasureTheory Set

/-- The canonical field of `h^α = h^ℂ - α log|·|` is a measurable function of the sample. -/
theorem measurable_alphaCanon {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} (hh : IsWholePlaneGFF P hC hcirc) (α : ℝ) :
    Measurable (alphaCanon α hC) := by
  have h : alphaCanon α hC = transl (logDrift α) ∘ (fun ω (i : CanonIdx) => hC ω i.1) :=
    funext (alphaCanon_eq α hC)
  rw [h]
  exact (measurable_transl _).comp (measurable_canonical hh)

/-- The law of the canonical field of `h^α = h^ℂ - α log|·|` is the same for any two whole-plane GFF models. -/
theorem map_alphaCanon_eq_of_isWholePlaneGFF {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (hh' : IsWholePlaneGFF P' hC' hcirc') (α : ℝ) :
    P.map (alphaCanon α hC) = P'.map (alphaCanon α hC') := by
  have h : alphaCanon α hC = transl (logDrift α) ∘ (fun ω (i : CanonIdx) => hC ω i.1) :=
    funext (alphaCanon_eq α hC)
  have h' : alphaCanon α hC' = transl (logDrift α) ∘ (fun ω (i : CanonIdx) => hC' ω i.1) :=
    funext (alphaCanon_eq α hC')
  rw [h, h', ← Measure.map_map (measurable_transl _) (measurable_canonical hh),
    ← Measure.map_map (measurable_transl _) (measurable_canonical hh'), canonicalLaw_eq_of_isWholePlaneGFF hh hh']

/-- A measurable set of canonical fields containing the canonical field of `h^α` almost surely under one whole-plane GFF
model contains it almost surely under every model. -/
theorem ae_alphaCanon_mem_of_isWholePlaneGFF {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    {P : Measure Ω} {P' : Measure Ω'} [IsProbabilityMeasure P] [IsProbabilityMeasure P']
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {hC' : Ω' → (ℂ → ℝ) → ℝ} {hcirc' : Ω' → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (hh' : IsWholePlaneGFF P' hC' hcirc') (α : ℝ)
    {G : Set (ModConstTestPairings (univ : Set ℂ))} (hG : MeasurableSet G)
    (hP : ∀ᵐ ω ∂P, alphaCanon α hC ω ∈ G) : ∀ᵐ ω ∂P', alphaCanon α hC' ω ∈ G := by
  have hmap := map_alphaCanon_eq_of_isWholePlaneGFF hh hh' α
  have h1 : ∀ᵐ L ∂(P.map (alphaCanon α hC)), L ∈ G :=
    (ae_map_iff (p := fun L => L ∈ G) (measurable_alphaCanon hh α).aemeasurable hG).2 hP
  rw [hmap] at h1
  exact (ae_map_iff (p := fun L => L ∈ G) (measurable_alphaCanon hh' α).aemeasurable hG).1 h1

end HarmonicBalls
