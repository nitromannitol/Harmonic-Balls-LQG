import Mathlib
import HarmonicBalls.FirstPass.S11u
import HarmonicBalls.FirstPass.Phase2.LQGMeasureLocalityDerived
import HarmonicBalls.FirstPass.Phase2.SquareMeasurableDerived
import HarmonicBalls.FirstPass.Phase2.InnerMeasurableDerived

/-!
# Derived circle-average locality link and the locality of the LQG measure (Fact 2.1 II)


* `lqgCircleAverageLocalityLink_derived`: `LQGCircleAverageLocalityLink` (the link hypothesis of
  `lqgMeasureLocality_of_circleLink`) under the whole-plane GFF premise `IsWholePlaneGFF P hC hcirc`.
  The link is a predicate of the model (`LQGMeasureLocalityDerived.lean:28`); it is proved here for whole-plane GFF
  models. `LQGMeasureLocality` itself carries `IsWholePlaneGFF` as a premise.
* `lqgMeasureLocality_of_gffCircleLink`: the proof of `lqgMeasureLocality_of_circleLink` with the link
  relativised to the GFF premise (the only use of `hlink` is in `hWk`, where `hGFF` is in scope).
* `lqgMeasureLocality_derived`: the forall-closure of `LQGMeasureLocality` (`Proposed/LQG.lean:97`).
* `lqgMeasureSquareMeasurable_derived'` and `lqgMassInnerMeasurable_derived'`: the binder-free
  forms of `lqgMeasureSquareMeasurable_derived` and `lqgMassInnerMeasurable_derived`.
-/

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace HarmonicBalls

noncomputable section

universe u

/-- The σ-algebra `σ(h|_U)` contains the pairings `hC · φ` with test functions `φ` supported in `U`, up to the
deterministic shift `α₀ ∫ φ log|·|`: `ω ↦ hC ω φ` is `σ(h|_U)`-measurable. -/
theorem measurable_gff_pairing {Ω : Type*} [MeasurableSpace Ω] (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ)
    (U : Set ℂ) (φ : ℂ → ℝ) (hφ : IsTestFunction U φ) :
    @Measurable Ω ℝ (fieldSigmaAlgebra α₀ hC U) _ (fun ω => hC ω φ) := by
  have h1 : MeasurableSpace.comap (fun ω => fieldPairing α₀ (hC ω) φ) inferInstance ≤
      fieldSigmaAlgebra α₀ hC U := by
    unfold fieldSigmaAlgebra
    exact le_iSup₂ (f := fun (ψ : ℂ → ℝ) (_ : IsTestFunction U ψ) =>
      MeasurableSpace.comap (fun ω => fieldPairing α₀ (hC ω) ψ) inferInstance) φ hφ
  have h2 : @Measurable Ω ℝ (fieldSigmaAlgebra α₀ hC U) _ (fun ω => fieldPairing α₀ (hC ω) φ) :=
    Measurable.of_comap_le h1
  have h3 := h2.add_const (α₀ * ∫ x, φ x * Real.log ‖x‖)
  convert h3 using 1
  funext ω
  simp [fieldPairing]

/-- **Circle-average locality link** (`LQGCircleAverageLocalityLink`, `LQGMeasureLocalityDerived.lean:28`), derived
from the whole-plane GFF premise. Route: `IsProbabilityMeasure P` from `IsWholePlaneGFF.isProbabilityMeasure`;
`wholePlaneCircleAverageLimit_derived` with `O := U` (the sphere lies in the closed ball, hence in `U`) gives test
functions `ψ j` supported in `U` with `hC ω (ψ j) → hcirc ω r z` a.s.; each `hC · (ψ j)` is `σ(h|_U)`-measurable;
the limit `limUnder` is measurable (`StronglyMeasurable.limUnder`), and `fieldCircleAverage α₀ (hcirc ω) r z` is this
limit minus the deterministic constant `α₀ · circleAverage (log ‖·‖) z r`. -/
theorem lqgCircleAverageLocalityLink_derived {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
    (α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (hGFF : IsWholePlaneGFF P hC hcirc) :
    LQGCircleAverageLocalityLink P α₀ hC hcirc := by
  intro U hU r z hr hsub
  have := hGFF.isProbabilityMeasure
  obtain ⟨ψ, hψ, hconv⟩ := wholePlaneCircleAverageLimit_derived.{u} Ω P hC hcirc hGFF U r z hU hr
    (Metric.sphere_subset_closedBall.trans hsub)
  refine ⟨fun ω => limUnder atTop (fun j => hC ω (ψ j)) -
    α₀ * Real.circleAverage (fun x => Real.log ‖x‖) z r, ?_, ?_⟩
  · have hm : ∀ j, @Measurable Ω ℝ (fieldSigmaAlgebra α₀ hC U) _ (fun ω => hC ω (ψ j)) :=
      fun j => measurable_gff_pairing α₀ hC U (ψ j) (hψ j).1
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    exact ((StronglyMeasurable.limUnder (l := atTop)
      (fun j => (hm j).stronglyMeasurable)).measurable).sub_const _
  · filter_upwards [hconv] with ω hω
    simp only [fieldCircleAverage]
    rw [hω.limUnder_eq]

/-- Fact 2.1 II (locality), with the circle-average link relativised to the whole-plane GFF premise. The proof is that of
`lqgMeasureLocality_of_circleLink` (`LQGMeasureLocalityDerived.lean:321`); the only use of the link is at `hWk`,
where `hGFF` is in scope. -/
theorem lqgMeasureLocality_of_gffCircleLink {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (γ α₀ : ℝ) (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ)
    (hlink : IsWholePlaneGFF P hC hcirc → LQGCircleAverageLocalityLink P α₀ hC hcirc) :
    LQGMeasureLocality P γ α₀ hC hcirc := by
  unfold LQGMeasureLocality
  intro hGFF _ _ _ μ hμ U hU
  obtain ⟨H, hHc, _, hHae⟩ := hGFF.exists_jointlyMeasurable_circleAverage
  have hGc : ∀ (ω : Ω) (k : ℕ),
      Continuous (fun z => fieldCircleAverage α₀ (H ω) (dyadicScale k) z) := by
    intro ω k
    unfold fieldCircleAverage
    exact (hHc ω _ (dyadicScale_pos k)).sub
      (continuous_const.mul (HarmonicBalls.MassFunctionalDerived.continuous_circleAverage_log_norm (dyadicScale_pos k)))
  -- one grid version per dyadic scale, on the cells well inside `U`
  have hWk : ∀ k : ℕ, ∃ Ψ : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ (@Prod.instMeasurableSpace Ω ℂ (fieldSigmaAlgebra α₀ hC U) _) _
        (fun p => Ψ p.1 p.2) ∧
      ∀ᵐ ω ∂P, ∀ z ∈ {z : ℂ | dyadicScale k < dCompl U z},
        Ψ ω z = fieldCircleAverage α₀ (H ω) (dyadicScale k) z := by
    intro k
    obtain ⟨Ψ, hΨm, hΨ⟩ := exists_grid_version P (fieldSigmaAlgebra α₀ hC U)
      (fun ω z => fieldCircleAverage α₀ (H ω) (dyadicScale k) z) (fun ω => hGc ω k)
      {z : ℂ | dyadicScale k < dCompl U z} (isOpen_lt continuous_const (dCompl_continuous U))
      (by
        intro z hz
        obtain ⟨g, hgm, hg⟩ := hlink hGFF U hU (dyadicScale k) z (dyadicScale_pos k)
          (ball_subset_of_lt_dCompl hz)
        refine ⟨g, hgm, ?_⟩
        filter_upwards [hHae, hg] with ω hω1 hω2
        show fieldCircleAverage α₀ (H ω) (dyadicScale k) z = g ω
        rw [← hω2]
        simp only [fieldCircleAverage, hω1])
    exact ⟨Ψ, hΨm, hΨ⟩
  choose Ψ hΨm hΨ using hWk
  have hm : ∀ n k : ℕ, @Measurable Ω ℝ≥0∞ (fieldSigmaAlgebra α₀ hC U) _
      (densityIntegral γ U n k (Ψ k)) := by
    intro n k
    exact measurable_lintegral_of_prod (fieldSigmaAlgebra α₀ hC U)
      (fun ω z => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) * Real.exp (γ * Ψ k ω z)) *
        ENNReal.ofReal (exhaustFn U n z))
      (measurable_density_prod (fieldSigmaAlgebra α₀ hC U) (Ψ k) (hΨm k)
        (dyadicScale k ^ (γ ^ 2 / 2)) γ (exhaustFn U n) (exhaustFn_continuous U n))
  have hμ' : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
  have hgood : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) ∧
      (∀ r z, H ω r z = hcirc ω r z) ∧
      ∀ k : ℕ, ∀ z ∈ {z : ℂ | dyadicScale k < dCompl U z},
        Ψ k ω z = fieldCircleAverage α₀ (H ω) (dyadicScale k) z := by
    filter_upwards [hμ', hHae, ae_all_iff.mpr hΨ] with ω h1 h2 h3
    exact ⟨h1, h2, h3⟩
  refine ⟨fun ω => ⨆ n : ℕ, limsup (fun k : ℕ => densityIntegral γ U n k (Ψ k) ω) atTop,
    Measurable.iSup fun n => Measurable.limsup fun k => hm n k, ?_⟩
  filter_upwards [hgood] with ω hω
  obtain ⟨h1, h2, h3⟩ := hω
  have hcontω : ∀ k : ℕ, Continuous (fieldCircleAverage α₀ (hcirc ω) (dyadicScale k)) := by
    intro k
    have hfun : fieldCircleAverage α₀ (hcirc ω) (dyadicScale k)
        = fieldCircleAverage α₀ (H ω) (dyadicScale k) := by
      funext z
      simp only [fieldCircleAverage, h2]
    rw [hfun]
    exact hGc ω k
  have hstep : ∀ n : ℕ, Tendsto (fun k : ℕ => densityIntegral γ U n k (Ψ k) ω) atTop
      (𝓝 (∫⁻ z, ENNReal.ofReal (exhaustFn U n z) ∂(μ ω))) := by
    intro n
    have hT := tendsto_lintegral_of_isLQGLimit h1 hcontω (exhaustFn_continuous U n)
      (exhaustFn_hasCompactSupport U n) (exhaustFn_nonneg U n)
    have hT0 : Tendsto (fun k : ℕ => dyadicScale k * n) atTop (𝓝 0) := by
      have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 2⁻¹)
        (by norm_num : (2 : ℝ)⁻¹ < 1)).mul_const (n : ℝ)
      rw [zero_mul] at h
      exact h
    have hev := hT0.eventually (gt_mem_nhds zero_lt_one)
    refine hT.congr' ?_
    filter_upwards [hev] with k hk
    have hk' : (n : ℝ) * dyadicScale k ≤ 1 := by rw [mul_comm]; exact hk.le
    have hρ : Measurable (fun z => ENNReal.ofReal (dyadicScale k ^ (γ ^ 2 / 2) *
        Real.exp (γ * fieldCircleAverage α₀ (hcirc ω) (dyadicScale k) z))) :=
      ENNReal.measurable_ofReal.comp (measurable_const.mul
        (Real.measurable_exp.comp (measurable_const.mul (hcontω k).measurable)))
    have hfm : Measurable (fun z => ENNReal.ofReal (exhaustFn U n z)) :=
      ENNReal.measurable_ofReal.comp (exhaustFn_continuous U n).measurable
    unfold densityIntegral lqgApprox
    rw [lintegral_withDensity_eq_lintegral_mul _ hρ hfm]
    apply lintegral_congr
    intro z
    simp only [Pi.mul_apply]
    by_cases hz : dyadicScale k < dCompl U z
    · have hfc : fieldCircleAverage α₀ (hcirc ω) (dyadicScale k) z
          = fieldCircleAverage α₀ (H ω) (dyadicScale k) z := by
        simp only [fieldCircleAverage, h2]
      rw [h3 k z hz, hfc]
    · have hf0 : exhaustFn U n z = 0 := by
        by_contra hne
        exact hz (lt_dCompl_of_exhaustFn_ne_zero hk' hne)
      simp [hf0]
  have hμU := tendsto_lintegral_exhaustFn (μ ω) hU
  have hmono : Monotone (fun n : ℕ => ∫⁻ z, ENNReal.ofReal (exhaustFn U n z) ∂(μ ω)) :=
    fun n m hnm => lintegral_mono fun z => ENNReal.ofReal_le_ofReal (exhaustFn_mono U z hnm)
  have hsup : μ ω U = ⨆ n : ℕ, ∫⁻ z, ENNReal.ofReal (exhaustFn U n z) ∂(μ ω) :=
    tendsto_nhds_unique hμU (tendsto_atTop_iSup hmono)
  show μ ω U = ⨆ n : ℕ, limsup (fun k : ℕ => densityIntegral γ U n k (Ψ k) ω) atTop
  rw [hsup]
  exact iSup_congr fun n => ((hstep n).limsup_eq).symm

/-- **Locality of the LQG measure** (`LQGMeasureLocality`, `Proposed/LQG.lean:97`), in its universally
quantified form. -/
theorem lqgMeasureLocality_derived : ∀ (γ α₀ : ℝ) (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ), LQGMeasureLocality P γ α₀ hC hcirc :=
  fun γ α₀ _ _ P hC hcirc => lqgMeasureLocality_of_gffCircleLink P γ α₀ hC hcirc
    (fun hGFF => lqgCircleAverageLocalityLink_derived P α₀ hC hcirc hGFF)

/-- `LQGMeasureSquareMeasurableFrozen`, binder-free: `lqgMeasureSquareMeasurable_derived` with the
locality input `lqgMeasureLocality_derived`. -/
theorem lqgMeasureSquareMeasurable_derived' : LQGMeasureSquareMeasurableFrozen.{u} :=
  lqgMeasureSquareMeasurable_derived.{u} (fun γ α₀ Ω _ P hC hcirc =>
    lqgMeasureLocality_derived γ α₀ Ω P hC hcirc)

/-- `LQGMassInnerMeasurableFrozen`, binder-free: `lqgMassInnerMeasurable_derived` with the locality input
`lqgMeasureLocality_derived`. -/
theorem lqgMassInnerMeasurable_derived' : LQGMassInnerMeasurableFrozen.{u} :=
  lqgMassInnerMeasurable_derived.{u} (fun Ω _ P _ γ α₀ hC hcirc =>
    lqgMeasureLocality_derived γ α₀ Ω P hC hcirc)

end

end HarmonicBalls
