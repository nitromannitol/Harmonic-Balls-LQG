import HarmonicBalls.FirstPass.S8c.RootCover
import HarmonicBalls.FirstPass.Frozen.S8c
import HarmonicBalls.Proposed.LQG

/-! # The Weyl comparison off the origin and the final root-side statement (FIRST-PASS fp-S8c-8-2-local, step W)

The comparison `hW` of `μ(ω)|_{B_1}` with `λ(ω)|_{B_1}`, used by `localRoot_ae_eventually_count_of_weyl`, is derived
from the FROZEN Weyl relation off the origin `LocalLQGInsertionWeylOffOrigin` (`Frozen/S8c.lean`) and the
non-atomicity of `μ(ω)` at `0` (`LQGMeasureNonatomic`, Proposed/LQG.lean, an explicit literature input pending
source-check). No other input is used.
-/

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

universe u

/-- A measurable null set for `lam` is `μ`-null, given the density off the origin and non-atomicity at `0`. -/
theorem measure_eq_zero_of_lam_eq_zero (μ lam : Measure ℂ) {f : ℂ → ℝ≥0∞}
    (hfm : Measurable f) (hf : ∀ z : ℂ, z ≠ 0 → 0 < f z)
    (hW : ∀ s : Set ℂ, MeasurableSet s → (0 : ℂ) ∉ s → lam s = ∫⁻ z in s, f z ∂μ)
    (h0 : μ {0} = 0) {M : Set ℂ} (hM : MeasurableSet M) (hlam : lam M = 0) : μ M = 0 := by
  have ht : MeasurableSet (M \ {0}) := hM.diff (measurableSet_singleton 0)
  have h0t : (0 : ℂ) ∉ M \ {0} := fun h => h.2 (Set.mem_singleton_iff.mpr rfl)
  have hlam_t : lam (M \ {0}) = 0 := measure_mono_null Set.sdiff_subset hlam
  rw [hW _ ht h0t] at hlam_t
  have h1 : ∀ᵐ z ∂(μ.restrict (M \ {0})), f z = 0 :=
    (lintegral_eq_zero_iff' hfm.aemeasurable).mp hlam_t
  have h2 : ∀ᵐ z ∂(μ.restrict (M \ {0})), z ∈ M \ {0} := ae_restrict_mem ht
  have h3 : ∀ᵐ z ∂(μ.restrict (M \ {0})), False := by
    filter_upwards [h1, h2] with z hz1 hz2
    have hz0 : z ≠ 0 := fun h => hz2.2 (Set.mem_singleton_iff.mpr h)
    exact absurd hz1 (hf z hz0).ne'
  have hres : μ.restrict (M \ {0}) = 0 := by
    have h4 := ae_iff.mp h3
    simpa using h4
  have hμt : μ (M \ {0}) = 0 := by
    have := congrArg (fun m : Measure ℂ => m (M \ {0})) hres
    simpa [Measure.restrict_apply_self] using this
  exact measure_mono_null (fun x hx => by
    by_cases hx0 : x = 0
    · exact Or.inr (Set.mem_singleton_iff.mpr hx0)
    · exact Or.inl ⟨hx, fun h => hx0 (Set.mem_singleton_iff.mp h)⟩) (measure_union_null hμt h0)

/-- Absolute continuity of the restrictions to a Borel set, from a density off the origin and non-atomicity. -/
theorem absCont_restrict_of_density_off_origin (μ lam : Measure ℂ) {f : ℂ → ℝ≥0∞}
    (hfm : Measurable f) (hf : ∀ z : ℂ, z ≠ 0 → 0 < f z)
    (hW : ∀ s : Set ℂ, MeasurableSet s → (0 : ℂ) ∉ s → lam s = ∫⁻ z in s, f z ∂μ)
    (h0 : μ {0} = 0) {B : Set ℂ} (hB : MeasurableSet B) :
    μ.restrict B ≪ lam.restrict B := by
  unfold Measure.AbsolutelyContinuous
  intro s hls
  rw [Measure.restrict_apply' hB] at hls ⊢
  set M := toMeasurable lam (s ∩ B) ∩ B with hM_def
  have hMm : MeasurableSet M := (measurableSet_toMeasurable _ _).inter hB
  have hsM : s ∩ B ⊆ M := fun x hx => ⟨subset_toMeasurable _ _ hx, hx.2⟩
  have hlamM : lam M = 0 :=
    measure_mono_null Set.inter_subset_left (by rw [measure_toMeasurable]; exact hls)
  exact measure_mono_null hsM (measure_eq_zero_of_lam_eq_zero μ lam hfm hf hW h0 hMm hlamM)

/-- The local rooted-law comparison `hW`, almost surely, from the frozen Weyl relation and non-atomicity. -/
theorem localRoot_weyl_ae (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ lam : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hlam : IsLQGMeasureOfField P γ 0 hcirc lam)
    (hN : LQGMeasureNonatomic P γ α₀ hC hcirc) :
    ∀ᵐ ω ∂P, (μ ω).restrict (ball 0 1) ≪ (lam ω).restrict (ball 0 1) := by
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  filter_upwards [hWeyl Ω P γ α₀ hC hcirc μ lam hGFF hγ0 hγ2 hα hμ hlam,
    hN hGFF hγ0 hγ2 hα μ hμ] with ω hω hNω
  refine absCont_restrict_of_density_off_origin (μ ω) (lam ω)
    (f := fun z : ℂ => ENNReal.ofReal (‖z‖ ^ (γ * α₀))) ?_ ?_ hω (hNω 0) measurableSet_ball
  · exact ENNReal.measurable_ofReal.comp (measurable_norm.pow_const _)
  · intro z hz
    exact ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos (norm_pos_iff.mpr hz) _)

/-- The root-side statement of Lemma 8.2 on the unit ball, with the Weyl comparison and non-atomicity derived. -/
theorem localRoot_ae_eventually_count_final (hL1 : LocalRootedFieldMeasureDomination.{u})
    (hfull : LQGMeasureFullSupportStmt.{u}) (hWeyl : LocalLQGInsertionWeylOffOrigin.{u})
    {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω) (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (hcirc : Ω → ℝ → ℂ → ℝ) (μ ν lam : Ω → Measure ℂ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hγ0 : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) (hν : IsLQGMeasureOfField P γ γ hcirc ν)
    (hlam : IsLQGMeasureOfField P γ 0 hcirc lam)
    (hN : LQGMeasureNonatomic P γ α₀ hC hcirc)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ) (ha : 0 < a)
    (hL3 : ∀ j : ℕ, 1 ≤ j → ∀ᵐ x ∂((volume.restrict (localDomain j)).prod P),
      localReferenceObservation ν j x ∈ recentredGoodSet β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω).restrict (ball 0 1),
      ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
        (veryGoodComparableScaleCount (μ ω) β z N₀ a b C₁m C₁p C₂m C₂p C₃ m N : ℝ) := by
  have : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hW := localRoot_weyl_ae hWeyl P γ α₀ hC hcirc μ lam hGFF hγ0 hγ2 hα hμ hlam hN
  have hN0 : ∀ᵐ ω ∂P, μ ω {0} = 0 :=
    (hN hGFF hγ0 hγ2 hα μ hμ).mono fun ω h => h 0
  exact localRoot_ae_eventually_count_of_weyl hL1 hfull P γ α₀ hC hcirc μ ν lam hGFF hγ0 hγ2 hα
    hμ hν hlam β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ ha hL3 hW hN0

#print axioms localRoot_ae_eventually_count_final

end HarmonicBalls
