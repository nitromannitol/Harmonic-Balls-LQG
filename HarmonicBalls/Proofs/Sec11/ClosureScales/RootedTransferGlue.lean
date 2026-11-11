import Mathlib

/-!
# Fubini glue for the rooted (marked) transfer of pinch frequencies (Section 11)

Written argument draft lines 565-649: the marked whole-plane GMC identity
`P(dg) μ_g(dz) = Law(g^{[z]}, z) d²z` on `B_1` (DMS21 Lemma A.10, marked version; cited by the draft, not yet a Lean
input) is combined with the rooted almost-sure statements for Lebesgue-a.e. root `z` to give the almost-sure statement
for `μ_ω`-a.e. point `z`. This file proves only that measure-theoretic step.

* The marked identity is an explicit hypothesis `hmarked`, in the form
  `∫ P(dω) ∫_{B_1} F(ω, z) μ_ω(dz) = ∫_{B_1} dz ∫ P(dω) F(shift z ω, z)`, with `shift z ω` the marked field.
* The rooted statement `hrooted` is needed only for Lebesgue-a.e. `z ∈ B_1`, for P-a.e. `ω`.
* Joint measurability of the bad set is the standard hypothesis `hbad`; measurability of the inner integral is `hmeasG`
  (draft 635-649, the Fubini hypotheses).

No new mathematics: the proof is `lintegral_eq_zero_iff'` on both sides of the marked identity.

The module credits no LatticeProb code.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal

/-- Draft 565-649: if, for Lebesgue-a.e. root `z` in `B_1`, the rooted field `shift z ω` is good for P-a.e. `ω`, and the
marked identity holds, then for P-a.e. `ω` the set of bad points `z` has `μ_ω`-measure zero in `B_1`. -/
theorem ae_ae_of_marked_identity_of_rooted_null
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (shift : ℂ → Ω → Ω) (bad : Ω → ℂ → Prop)
    (hbad : MeasurableSet {p : Ω × ℂ | bad p.1 p.2})
    (hmarked : ∀ F : Ω × ℂ → ℝ≥0∞, Measurable F →
      ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, F (ω, z) ∂(μ ω) ∂P =
        ∫⁻ z in ball (0 : ℂ) 1, ∫⁻ ω, F (shift z ω, z) ∂P)
    (hmeasG : Measurable fun ω => ∫⁻ z in ball (0 : ℂ) 1,
      Set.indicator {p : Ω × ℂ | bad p.1 p.2} 1 (ω, z) ∂(μ ω))
    (hrooted : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)), ∀ᵐ ω ∂P, ¬ bad (shift z ω) z) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂((μ ω).restrict (ball (0 : ℂ) 1)), ¬ bad ω z := by
  set F : Ω × ℂ → ℝ≥0∞ := Set.indicator {p : Ω × ℂ | bad p.1 p.2} 1 with hF
  have hFm : Measurable F := measurable_const.indicator hbad
  have h0 : ∫⁻ ω, ∫⁻ z in ball (0 : ℂ) 1, F (ω, z) ∂(μ ω) ∂P = 0 := by
    rw [hmarked F hFm]
    have hinner : ∀ᵐ z ∂(volume.restrict (ball (0 : ℂ) 1)),
        ∫⁻ ω, F (shift z ω, z) ∂P = 0 := by
      filter_upwards [hrooted] with z hz
      have hzero : ∀ᵐ ω ∂P, F (shift z ω, z) = 0 := by
        filter_upwards [hz] with ω hω
        simp [hF, hω]
      rw [lintegral_congr_ae hzero]
      simp
    rw [lintegral_congr_ae hinner]
    simp
  have hG : ∀ᵐ ω ∂P, ∫⁻ z in ball (0 : ℂ) 1, F (ω, z) ∂(μ ω) = 0 :=
    (lintegral_eq_zero_iff' hmeasG.aemeasurable).1 h0
  filter_upwards [hG] with ω hω
  have hzF : ∀ᵐ z ∂((μ ω).restrict (ball (0 : ℂ) 1)), F (ω, z) = 0 :=
    (lintegral_eq_zero_iff' (hFm.comp measurable_prodMk_left).aemeasurable).1 hω
  filter_upwards [hzF] with z hz
  intro hbz
  have : F (ω, z) = 1 := by simp [hF, hbz]
  rw [this] at hz
  exact one_ne_zero hz

end HarmonicBalls
