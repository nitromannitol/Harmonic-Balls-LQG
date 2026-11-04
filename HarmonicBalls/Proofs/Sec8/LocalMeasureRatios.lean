import HarmonicBalls.Proofs.Sec8.GoodEventMeasurable
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw

/-! # Local representatives from normalized masses

Normalizing the restriction to a ball eliminates the field's additive constant.
Measurability of its open-set mass ratios supplies a measurable representative.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal

namespace HarmonicBalls

/-- The restriction of a measure to a set, normalized by its total mass. -/
noncomputable def normalizedRestriction (μ : Measure ℂ) (U : Set ℂ) : Measure ℂ :=
  (μ U)⁻¹ • μ.restrict U

/-- A normalized restriction is finite, including when its original mass is
zero or infinite. -/
instance normalizedRestriction_isFiniteMeasure (μ : Measure ℂ) (U : Set ℂ) :
    IsFiniteMeasure (normalizedRestriction μ U) := by
  unfold normalizedRestriction
  simpa only [Measure.restrict_apply_univ] using
    (inferInstance : IsFiniteMeasure (((μ.restrict U) univ)⁻¹ • μ.restrict U))

/-- Normalized masses on any generating π-system containing the whole
space determine a measurable normalized restriction. -/
theorem measurable_normalizedRestriction_of_piSystem {Ω : Type*} [MeasurableSpace Ω]
    (μ : Ω → Measure ℂ) (U : Set ℂ) (S : Set (Set ℂ))
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ V ∈ S, MeasurableSet V) (huniv : univ ∈ S)
    (h : ∀ V ∈ S, Measurable (fun ω => μ ω (V ∩ U) / μ ω U)) :
    Measurable (fun ω => normalizedRestriction (μ ω) U) := by
  apply Measurable.measure_of_isPiSystem hgen hpi
  · intro V hV
    simpa only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply (hsets V hV), ENNReal.div_eq_inv_mul] using h V hV
  · simpa only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply_univ, univ_inter, ENNReal.div_eq_inv_mul] using h univ huniv

/-- Measurability of normalized masses on open sets determines the entire
normalized restriction as a measure-valued map. -/
theorem measurable_normalizedRestriction {Ω : Type*} [MeasurableSpace Ω]
    (μ : Ω → Measure ℂ) (U : Set ℂ)
    (h : ∀ V : Set ℂ, IsOpen V →
      Measurable (fun ω => μ ω (V ∩ U) / μ ω U)) :
    Measurable (fun ω => normalizedRestriction (μ ω) U) := by
  apply Measurable.measure_of_isPiSystem BorelSpace.measurable_eq isPiSystem_isOpen
  · intro V hV
    change IsOpen V at hV
    simpa only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply hV.measurableSet, ENNReal.div_eq_inv_mul] using h V hV
  · simpa only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
      Measure.restrict_apply_univ, univ_inter, ENNReal.div_eq_inv_mul] using h univ isOpen_univ

/-- A nonzero finite mass reconstructs a measure from its normalized
restriction, up to multiplication by that mass. -/
theorem restrict_eq_smul_normalizedRestriction (μ : Measure ℂ) {U : Set ℂ}
    (hU : MeasurableSet U) (hzero : μ U ≠ 0) (htop : μ U ≠ ∞) :
    μ.restrict U = μ U • (normalizedRestriction μ U).restrict U := by
  rw [normalizedRestriction, Measure.restrict_smul, Measure.restrict_restrict hU, inter_self,
    smul_smul, ENNReal.mul_inv_cancel hzero htop, one_smul]

/-- Full support and local finiteness make every positive-radius reference
ball have nonzero finite mass on a common almost-sure event. -/
theorem ae_referenceBall_pos_finite {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (μ : Ω → Measure ℂ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    (hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω)) :
    ∀ᵐ ω ∂P, ∀ ε, 0 < ε → μ ω (ball 0 ε) ≠ 0 ∧ μ ω (ball 0 ε) ≠ ∞ := by
  filter_upwards [hfull, hloc] with ω hωfull hωloc ε hε
  let : IsLocallyFiniteMeasure (μ ω) := hωloc
  exact ⟨(hωfull _ isOpen_ball ⟨0, mem_ball_self hε⟩).ne', measure_ball_ne_top⟩

/-- Measurable normalized local mass ratios give the representatives required
by the germ-local indicator argument. -/
theorem local_representatives_of_mass_ratios
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (germ : ℝ → MeasurableSpace Ω) (μ : Ω → Measure ℂ)
    (hratio : ∀ ε, 0 < ε → ∀ V : Set ℂ, IsOpen V →
      @Measurable Ω ℝ≥0∞ (germ ε) _
        (fun ω => μ ω (V ∩ ball 0 ε) / μ ω (ball 0 ε)))
    (hpositive : ∀ ε, 0 < ε → ∀ᵐ ω ∂P,
      μ ω (ball 0 ε) ≠ 0 ∧ μ ω (ball 0 ε) ≠ ∞) :
    ∀ ε, 0 < ε → ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (germ ε) _ ν ∧
      ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
        (μ ω).restrict (ball 0 ε) = c • (ν ω).restrict (ball 0 ε) := by
  intro ε hε
  refine ⟨fun ω => normalizedRestriction (μ ω) (ball 0 ε), ?_, ?_⟩
  · exact @measurable_normalizedRestriction Ω (germ ε) μ (ball 0 ε) (hratio ε hε)
  · filter_upwards [hpositive ε hε] with ω hω
    exact ⟨μ ω (ball 0 ε), hω.1, hω.2,
      restrict_eq_smul_normalizedRestriction (μ ω) isOpen_ball.measurableSet hω.1 hω.2⟩

/-- A generating π-system reduces the local-representative construction to
normalized masses on that system. In particular, a countable system yields
only countably many scalar measurability obligations. -/
theorem local_representatives_of_piSystem_mass_ratios
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (germ : ℝ → MeasurableSpace Ω) (μ : Ω → Measure ℂ)
    (S : Set (Set ℂ))
    (hgen : (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom S)
    (hpi : IsPiSystem S) (hsets : ∀ V ∈ S, MeasurableSet V) (huniv : univ ∈ S)
    (hratio : ∀ ε, 0 < ε → ∀ V ∈ S,
      @Measurable Ω ℝ≥0∞ (germ ε) _
        (fun ω => μ ω (V ∩ ball 0 ε) / μ ω (ball 0 ε)))
    (hpositive : ∀ ε, 0 < ε → ∀ᵐ ω ∂P,
      μ ω (ball 0 ε) ≠ 0 ∧ μ ω (ball 0 ε) ≠ ∞) :
    ∀ ε, 0 < ε → ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (germ ε) _ ν ∧
      ∀ᵐ ω ∂P, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ∞ ∧
        (μ ω).restrict (ball 0 ε) = c • (ν ω).restrict (ball 0 ε) := by
  intro ε hε
  refine ⟨fun ω => normalizedRestriction (μ ω) (ball 0 ε), ?_, ?_⟩
  · exact @measurable_normalizedRestriction_of_piSystem Ω (germ ε) μ (ball 0 ε)
      S hgen hpi hsets huniv (hratio ε hε)
  · filter_upwards [hpositive ε hε] with ω hω
    exact ⟨μ ω (ball 0 ε), hω.1, hω.2,
      restrict_eq_smul_normalizedRestriction (μ ω) isOpen_ball.measurableSet hω.1 hω.2⟩

end HarmonicBalls
