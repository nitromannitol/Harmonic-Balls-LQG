import HarmonicBalls.Proofs.Sec11.DyadicDiameterThreshold

/-! # Transfer of closed-square tail estimates to dyadic tiles

The closed-square bound is an explicit hypothesis; this module does not
assert the weak LQG metric estimate. -/

namespace HarmonicBalls
open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- The intermediate dyadic side lengths approach zero from above. -/
theorem tendsto_intermediate_square_side (L : ℝ) (hL : 0 < L) :
    Tendsto (fun n : ℕ => 3 * L / (2 * (2 : ℝ) ^ n)) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have ht := (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)).const_mul
          (3 * L / 2)
    have ht' : Tendsto (fun n : ℕ => (3 * L / 2) * (1 / 2 : ℝ) ^ n) atTop (𝓝 0) := by
      simpa using ht
    apply ht'.congr'
    filter_upwards with n
    rw [div_pow]
    field_simp
    ring
  · exact Filter.Eventually.of_forall fun n => by
      change 0 < 3 * L / (2 * (2 : ℝ) ^ n)
      positivity

/-- Sampling a small-scale error along the intermediate square sides preserves
the vanishing error. -/
theorem tendsto_intermediate_square_error (L : ℝ) (hL : 0 < L)
    (e : ℝ → ℝ) (he : Tendsto e (𝓝[>] 0) (𝓝 0)) :
    Tendsto (fun n : ℕ => e (3 * L / (2 * (2 : ℝ) ^ n))) atTop (𝓝 0) :=
  he.comp (tendsto_intermediate_square_side L hL)

/-- A uniform closed-square estimate at the intermediate scales transfers to
the enlarged-domain diameter with any smaller positive tail exponent. -/
theorem dyadicIntermediateInternalDiameter_tail_of_closed_square
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → ℂ → ℂ → ℝ) (a : ℂ) (L : ℝ) (hL : 0 < L)
    (threshold : ℕ → Ω → ℝ≥0∞) (p p' : ℝ) (hp' : 0 < p') (hpp : p' < p)
    (e : ℝ → ℝ) (he : Tendsto e (𝓝[>] 0) (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      P {ω | threshold n ω <
        ⨆ x ∈ complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i,
          ⨆ y ∈ complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i,
            internalMetric (D ω) (complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i) x y} ≤
      ENNReal.ofReal ((3 * L / (2 * (2 : ℝ) ^ n)) ^
        (p + e (3 * L / (2 * (2 : ℝ) ^ n))))) :
    ∀ᶠ n in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      P {ω | threshold n ω < dyadicIntermediateInternalDiameter D a L n i ω} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ (p' * n)) := by
  have he' := tendsto_intermediate_square_error L hL e he
  have hscale := dyadic_scaled_power_error_eventually_le (3 * L / 2) p p'
    (by positivity) hp' hpp (fun n => e (3 * L / (2 * (2 : ℝ) ^ n))) he'
  filter_upwards [hbound, hscale] with n hn hs
  intro i
  have hside : 3 * L / (2 * (2 : ℝ) ^ n) = (3 * L / 2) * (1 / 2 : ℝ) ^ n := by
    rw [div_pow]
    field_simp
    ring
  exact (dyadicIntermediateInternalDiameter_tail_le P D a L hL n i (threshold n)).trans
    ((hn i).trans (ENNReal.ofReal_le_ofReal (by simpa only [hside] using hs)))

/-- The explicit closed-square estimate supplies both the vanishing threshold
and the uniform dyadic tail required by the mass-diameter construction. -/
theorem dyadicIntermediateInternalDiameter_thresholds_of_closed_square
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (D : Ω → ℂ → ℂ → ℝ) (a : ℂ) (L : ℝ) (hL : 0 < L)
    (c s ξ : ℝ) (hs : 0 < s) (hcirc : Ω → ℝ → ℂ → ℝ)
    (p p' : ℝ) (hp' : 2 < p') (hpp : p' < p)
    (e : ℝ → ℝ) (he : Tendsto e (𝓝[>] 0) (𝓝 0))
    (hbound : ∀ᶠ n in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      P {ω | ENNReal.ofReal (c * (3 * L / (2 * (2 : ℝ) ^ n)) ^ s) *
          ENNReal.ofReal (Real.exp (ξ * hcirc ω 1 0)) <
        ⨆ x ∈ complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i,
          ⨆ y ∈ complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i,
            internalMetric (D ω) (complexIntermediateGridSquare a (L / (2 : ℝ) ^ n) i) x y} ≤
      ENNReal.ofReal ((3 * L / (2 * (2 : ℝ) ^ n)) ^
        (p + e (3 * L / (2 * (2 : ℝ) ^ n))))) :
    (∀ d : ℝ, 0 < d → ∀ᶠ n in atTop,
      ENNReal.ofReal (c * (3 * L / (2 * (2 : ℝ) ^ n)) ^ s) < ENNReal.ofReal d) ∧
    (∀ᶠ n in atTop, ∀ i : Fin (2 ^ n) × Fin (2 ^ n),
      P {ω | ENNReal.ofReal (c * (3 * L / (2 * (2 : ℝ) ^ n)) ^ s) *
          ENNReal.ofReal (Real.exp (ξ * hcirc ω 1 0)) <
        dyadicIntermediateInternalDiameter D a L n i ω} ≤
        ENNReal.ofReal ((1 / 2 : ℝ) ^ ((p' + (0 : ℝ)) * n))) := by
  refine ⟨fun d hd => intermediate_square_threshold_eventually_lt c L s hL hs d hd, ?_⟩
  have ht := dyadicIntermediateInternalDiameter_tail_of_closed_square P D a L hL
    (fun n ω => ENNReal.ofReal (c * (3 * L / (2 * (2 : ℝ) ^ n)) ^ s) *
      ENNReal.ofReal (Real.exp (ξ * hcirc ω 1 0))) p p' (by linarith) hpp e he hbound
  simpa only [add_zero] using ht

#print axioms dyadicIntermediateInternalDiameter_thresholds_of_closed_square
#print axioms tendsto_intermediate_square_side
#print axioms tendsto_intermediate_square_error
#print axioms dyadicIntermediateInternalDiameter_tail_of_closed_square
end HarmonicBalls
