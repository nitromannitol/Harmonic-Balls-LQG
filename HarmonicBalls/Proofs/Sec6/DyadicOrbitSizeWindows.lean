import HarmonicBalls.Proofs.Sec6.SingularDyadicSizeWindows

/-! # Size windows along dyadic orbits

The imported Section 6 assembly uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- For each positive phase, a single pair of size windows works along its
entire inverse dyadic orbit, uniformly in the centre and field realization. -/
theorem exists_universal_wholePlane_size_windows_dyadic_orbit
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ β : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {s : ℝ} (hs : 0 < s) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
        WholePlaneGFFAffineInvariance P hC hcirc → ∀ (n : ℕ) (z : ℂ),
      P {ω | annulusBallMassSize (μ ω) β (s * dyadicScale n) z /
        (μ ω) (annulus z ((s * dyadicScale n) / 4) (2 * (s * dyadicScale n))) ∉
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} ≤ δ ∧
      P {ω | annulusGreenPotentialSup (μ ω) z ((s * dyadicScale n) / 4) (2 * (s * dyadicScale n)) /
        (μ ω) (annulus z ((s * dyadicScale n) / 4) (2 * (s * dyadicScale n))) ∉
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, h⟩ :=
    exists_universal_wholePlane_size_windows_fixed_scale hgrowth hγ hγ₂ hβ P₀ h₀ hμ₀ hs hδ
  refine ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, ?_⟩
  intro Ω _ P hC hcirc μ hgff hμ hAff n z
  have hw := h Ω P hC hcirc μ hgff hμ hAff 0
  have hr : 0 < s * dyadicScale n := mul_pos hs (dyadicScale_pos n)
  have hscale : (2 : ℝ) ^ n * (s * dyadicScale n) = s := by
    have heq : (2 : ℝ) ^ n * dyadicScale n = 1 := by
      simpa only [zero_add, dyadicScale, pow_zero] using dyadicScale_shift n 0
    calc
      (2 : ℝ) ^ n * (s * dyadicScale n) = s * ((2 : ℝ) ^ n * dyadicScale n) := by ring
      _ = s := by rw [heq, mul_one]
  have hd₁ := (identDistrib_lqg_ballMassSizeRatio_dyadic hγ hgff hμ hAff n β hr).symm.trans
    (identDistrib_lqg_ballMassSizeRatio_translate_of_affine hgff hμ hAff β hr z)
  have hd₂ := (identDistrib_lqg_greenSizeRatio_dyadic hγ hgff hμ hAff n (s * dyadicScale n)).symm.trans
    (identDistrib_lqg_greenSizeRatio_translate_of_affine hgff hμ hAff (ρ := s * dyadicScale n) z)
  rw [hscale] at hd₁ hd₂
  have heq₁ := hd₁.symm.measure_mem_eq
    (measurableSet_Icc.compl : MeasurableSet (Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p))ᶜ)
  have heq₂ := hd₂.symm.measure_mem_eq
    (measurableSet_Icc.compl : MeasurableSet (Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p))ᶜ)
  exact ⟨heq₁ ▸ hw.1, heq₂ ▸ hw.2⟩

/-- The dyadic-orbit size windows also hold for singular LQG measures when
the annulus is separated from the origin. -/
theorem exists_universal_lqg_size_windows_dyadic_orbit
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ β : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {s : ℝ} (hs : 0 < s) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
        (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
        IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
        LQGMeasureExistence P γ 0 hC hcirc →
        WholePlaneGFFAffineInvariance P hC hcirc → ∀ (n : ℕ) (z : ℂ),
      (s * dyadicScale n) / 100 ≤ infDist (0 : ℂ)
        (annulus z ((s * dyadicScale n) / 4) (2 * (s * dyadicScale n))) →
      P {ω | annulusBallMassSize (μ ω) β (s * dyadicScale n) z /
        (μ ω) (annulus z ((s * dyadicScale n) / 4) (2 * (s * dyadicScale n))) ∉
        Icc (ENNReal.ofReal C₁m) (ENNReal.ofReal C₁p)} ≤ δ ∧
      P {ω | annulusGreenPotentialSup (μ ω) z ((s * dyadicScale n) / 4) (2 * (s * dyadicScale n)) /
        (μ ω) (annulus z ((s * dyadicScale n) / 4) (2 * (s * dyadicScale n))) ∉
        Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  obtain ⟨C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p, h⟩ :=
    exists_universal_wholePlane_size_windows_dyadic_orbit hgrowth hγ hγ₂ hβ P₀ h₀ hμ₀ hs hδ
  let e : ℝ := -(γ * α₀)
  let K : ℝ := ((401 : ℝ) ^ |e|) ^ 2
  have hK : 0 < K := sq_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨C₁m / K, K * C₁p, C₂m / K, K * C₂p,
    div_pos h₁m hK, mul_pos hK h₁p, div_pos h₂m hK, mul_pos hK h₂p, ?_⟩
  intro Ω _ P hC hcirc μ hgff hμ hEx hAff n z hd
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨ν, hν⟩ := hEx hgff hγ hγ₂ hQ
  have hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ := by
    have h1 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α₀ (hcirc ω)) (μ ω) := hμ
    filter_upwards [h1, lqgMeasureWeylScaling Ω P γ 0 hC hcirc hgff hγ hγ₂ hQ ν hν] with ω hω1 hω2
    exact restrict_compl_zero_eq_withDensity hω1 hω2
  have ht := size_window_failure_le_of_singular_weight P
    (β := β) (C₁m := C₁m) (C₁p := C₁p) (C₂m := C₂m) (C₂p := C₂p)
    (mul_pos hs (dyadicScale_pos n)) hd hweight
  have hw := h Ω P hC hcirc ν hgff hν hAff n z
  exact ⟨ht.1.trans hw.1, ht.2.trans hw.2⟩

end HarmonicBalls.Section6
