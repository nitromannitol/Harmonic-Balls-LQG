import HarmonicBalls.Defs.Notation

/-!
# The mixing measure on the dyadic scales

The probability measure `ν = mixMeasure` on `ℕ` with `ν{k} ∝ (k+1)⁻²`, used to mix the rescaled fields
`h^{(k)}` into one field on `ℕ × Ω` (HarmonicBalls/Steps/Sec2/VolumeGrowth.lean, `WholePlaneGFFMixtureStep`).
A bound for the mixture transfers to each `k` at the cost of the factor `ν{k}⁻¹ = S (k+1)²`
(`measure_slice_le`), and almost sure statements for every `k` hold for the mixture (`ae_mix_of_forall`).
-/

namespace HarmonicBalls

open MeasureTheory Set
open scoped ENNReal

/-- The weight `(k+1)⁻²`. -/
noncomputable def mixWeight (k : ℕ) : ℝ≥0∞ := ENNReal.ofReal (((k : ℝ) + 1) ^ 2)⁻¹

/-- The total weight `S = ∑ₖ (k+1)⁻²`. -/
noncomputable def mixMass : ℝ≥0∞ := ∑' k, mixWeight k

/-- The mixing probability measure `ν{k} = S⁻¹ (k+1)⁻²` on `ℕ`. -/
noncomputable def mixMeasure : Measure ℕ := mixMass⁻¹ • Measure.sum fun k => mixWeight k • Measure.dirac k

theorem summable_mixWeight : Summable fun k : ℕ => (((k : ℝ) + 1) ^ 2)⁻¹ := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_nat_pow_inv.2 one_lt_two)
  simpa [Nat.cast_add, Nat.cast_one] using h

theorem mixMass_ne_top : mixMass ≠ ∞ := by
  unfold mixMass mixWeight
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => by positivity) summable_mixWeight]
  exact ENNReal.ofReal_ne_top

theorem one_le_mixMass : 1 ≤ mixMass := by
  calc (1 : ℝ≥0∞) = mixWeight 0 := by simp [mixWeight]
    _ ≤ mixMass := ENNReal.le_tsum 0

theorem mixMass_ne_zero : mixMass ≠ 0 := (zero_lt_one.trans_le one_le_mixMass).ne'

theorem sum_apply_singleton (k : ℕ) :
    (Measure.sum fun j => mixWeight j • Measure.dirac j) {k} = mixWeight k := by
  rw [Measure.sum_apply _ (measurableSet_singleton k)]
  simp only [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply' _ (measurableSet_singleton k),
    indicator, mem_singleton_iff, Pi.one_apply, mul_ite, mul_one, mul_zero]
  rw [tsum_ite_eq]

theorem mixMeasure_singleton (k : ℕ) : mixMeasure {k} = mixMass⁻¹ * mixWeight k := by
  rw [mixMeasure, Measure.smul_apply, smul_eq_mul, sum_apply_singleton]

instance : IsProbabilityMeasure mixMeasure := by
  constructor
  rw [mixMeasure, Measure.smul_apply, smul_eq_mul, Measure.sum_apply _ MeasurableSet.univ]
  simp only [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  exact ENNReal.inv_mul_cancel mixMass_ne_zero mixMass_ne_top

/-- `ν{k}⁻¹ = S (k+1)²`. -/
theorem mixMeasure_singleton_inv (k : ℕ) :
    (mixMeasure {k})⁻¹ = ENNReal.ofReal (mixMass.toReal * ((k : ℝ) + 1) ^ 2) := by
  rw [mixMeasure_singleton, mixWeight, ENNReal.mul_inv (Or.inr ENNReal.ofReal_ne_top)
    (Or.inl (ENNReal.inv_ne_top.2 mixMass_ne_zero)), inv_inv, ENNReal.ofReal_inv_of_pos (by positivity),
    inv_inv, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal mixMass_ne_top]

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- A bound for the mixture at the slice `k`: `P{ω | (k, ω) ∈ S} ≤ ν{k}⁻¹ (ν ⊗ P)(S)`. -/
theorem measure_slice_le [SFinite P] (S : Set (ℕ × Ω)) (k : ℕ) :
    P {ω | (k, ω) ∈ S} ≤ ENNReal.ofReal (mixMass.toReal * ((k : ℝ) + 1) ^ 2) * (mixMeasure.prod P) S := by
  have hsub : ({k} : Set ℕ) ×ˢ {ω | (k, ω) ∈ S} ⊆ S := by
    rintro ⟨j, ω⟩ ⟨hj, hω⟩
    have hj' : j = k := hj
    subst hj'
    exact hω
  have h1 : mixMeasure {k} * P {ω | (k, ω) ∈ S} ≤ (mixMeasure.prod P) S := by
    rw [← Measure.prod_prod]; exact measure_mono hsub
  have hk0 : mixMeasure {k} ≠ 0 := by
    rw [mixMeasure_singleton]
    exact mul_ne_zero (ENNReal.inv_ne_zero.2 mixMass_ne_top) (by simp [mixWeight]; positivity)
  have hktop : mixMeasure {k} ≠ ∞ := measure_ne_top _ _
  rw [← mixMeasure_singleton_inv]
  calc P {ω | (k, ω) ∈ S} = (mixMeasure {k})⁻¹ * (mixMeasure {k} * P {ω | (k, ω) ∈ S}) := by
        rw [← mul_assoc, ENNReal.inv_mul_cancel hk0 hktop, one_mul]
    _ ≤ (mixMeasure {k})⁻¹ * (mixMeasure.prod P) S := by gcongr

/-- Almost sure statements for every slice hold for the mixture. -/
theorem ae_mix_of_forall [SFinite P] {p : ℕ → Ω → Prop} (h : ∀ k, ∀ᵐ ω ∂P, p k ω) :
    ∀ᵐ x ∂(mixMeasure.prod P), p x.1 x.2 := by
  rw [ae_iff]
  set N : ℕ → Set Ω := fun k => toMeasurable P {ω | ¬ p k ω}
  have hN : ∀ k, P (N k) = 0 := fun k => by rw [measure_toMeasurable]; exact ae_iff.1 (h k)
  refine measure_mono_null (t := ⋃ k, ({k} : Set ℕ) ×ˢ N k) ?_ (measure_iUnion_null fun k => ?_)
  · rintro ⟨k, ω⟩ hx
    exact mem_iUnion.2 ⟨k, mem_singleton k, subset_toMeasurable P _ hx⟩
  · rw [Measure.prod_prod, hN, mul_zero]

end HarmonicBalls
