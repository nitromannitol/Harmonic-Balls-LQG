import HarmonicBalls.Proofs.Sec6.BallMassPhaseProbability
import HarmonicBalls.Proofs.Sec6.DyadicOrbitSizeWindows
import HarmonicBalls.Proofs.Sec6.CompactPhaseProbability
import HarmonicBalls.Proofs.Sec6.AffineInvarianceAssembly

/-! # Uniform Ball-mass windows

The imported annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory ProbabilityTheory Metric Set Filter
open scoped ENNReal

universe u

/-- One Ball-mass window works at every radius and centre for every
whole-plane LQG realization, under volume growth. -/
theorem exists_universal_wholePlane_ballMassSize_window
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ β : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₂m C₂p : ℝ, 0 < C₂m ∧ 0 < C₂p ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
      ∀ ρ : ℝ, 0 < ρ → ∀ z : ℂ,
      P {ω | annulusBallMassSize (μ ω) β ρ z /
        (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
          Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  let : IsProbabilityMeasure P₀ := h₀.isProbabilityMeasure
  have heqβ : γ * (lqgQ γ - 0) = 2 + γ ^ 2 / 2 := by
    unfold lqgQ
    field_simp
    ring
  have hβ' : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - 0)) < β := by
    apply max_lt hβ
    rw [heqβ]
    nlinarith
  obtain ⟨lo, hi, hlo, hhi, hphase⟩ :=
    exists_ballMassSize_window_on_dyadic_phases hgrowth P₀ hγ hγ₂ hβ' h₀ hμ₀ hδ
  refine ⟨lo, hi, hlo, hhi, ?_⟩
  intro Ω _ P hC hcirc μ hgff hμ ρ hρ z
  have hAff := wholePlaneGFFAffineInvariance_proved P hC hcirc
  have hsmall : ∀ r : ℝ, 0 < r → r ≤ 1 → ∀ z : ℂ,
      P {ω | annulusBallMassSize (μ ω) β r z /
        (μ ω) (annulus z (r / 4) (2 * r)) ∉
          Icc (ENNReal.ofReal lo) (ENNReal.ofReal hi)} ≤ δ := by
    intro r hr hr1 w
    obtain ⟨s, n, hs, rfl⟩ := exists_dyadic_phase hr hr1
    have hspos : 0 < s := by linarith [hs.1]
    have heq : (2 : ℝ) ^ n * (s * dyadicScale n) = s := by
      have h : (2 : ℝ) ^ n * dyadicScale n = 1 := by
        simpa only [zero_add, dyadicScale, pow_zero] using dyadicScale_shift n 0
      calc
        (2 : ℝ) ^ n * (s * dyadicScale n) = s * ((2 : ℝ) ^ n * dyadicScale n) := by ring
        _ = s := by rw [h, mul_one]
    have hlaw := h₀.identDistrib_lqgMeasure_across_spaces hgff hμ₀ hμ
    have hd0 := (identDistrib_lqg_ballMassSizeRatio_dyadic hγ hgff hμ hAff n β (by positivity : 0 < s * dyadicScale n)).symm
    rw [heq] at hd0
    have hd := (hlaw.comp (measurable_annulusBallMassSize_ratio β s 0 hspos)).trans hd0
    have hd' := hd.trans (identDistrib_lqg_ballMassSizeRatio_translate_of_affine
      hgff hμ hAff β (by positivity : 0 < s * dyadicScale n) w)
    have hprob := hd'.symm.measure_mem_eq
      (measurableSet_Icc.compl : MeasurableSet (Icc (ENNReal.ofReal lo) (ENNReal.ofReal hi))ᶜ)
    exact hprob ▸ hphase s ⟨hs.1.le, hs.2⟩
  obtain ⟨n, hn⟩ := exists_nat_gt ρ
  have hnpow : (n : ℝ) ≤ (2 : ℝ) ^ n := by exact_mod_cast (Nat.le_of_lt n.lt_two_pow_self)
  have hn' : ρ ≤ (2 : ℝ) ^ n := le_trans hn.le hnpow
  let r : ℝ := ρ / (2 : ℝ) ^ n
  have hpow : (0 : ℝ) < (2 : ℝ) ^ n := by positivity
  have hr : 0 < r := div_pos hρ hpow
  have hr1 : r ≤ 1 := (div_le_one hpow).2 hn'
  have hscale : (2 : ℝ) ^ n * r = ρ := by dsimp [r]; field_simp
  have hd := identDistrib_lqg_ballMassSizeRatio_dyadic hγ hgff hμ hAff n β hr
  rw [hscale] at hd
  have ht₁ := identDistrib_lqg_ballMassSizeRatio_translate_of_affine hgff hμ hAff β hr z
  have ht₂ := identDistrib_lqg_ballMassSizeRatio_translate_of_affine hgff hμ hAff β hρ z
  have hdist := ht₁.symm.trans (hd.trans ht₂)
  have heq := hdist.symm.measure_mem_eq
    (measurableSet_Icc.compl : MeasurableSet (Icc (ENNReal.ofReal lo) (ENNReal.ofReal hi))ᶜ)
  exact heq ▸ hsmall r hr hr1 z

/-- The Ball-mass window extends to singular fields on annuli separated
from the singularity, using zero-strength LQG existence. -/
theorem exists_universal_lqg_ballMassSize_window
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α β : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] (P₀ : Measure Ω₀)
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ C₂m C₂p : ℝ, 0 < C₂m ∧ 0 < C₂p ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      LQGMeasureExistence P γ 0 hC hcirc → ∀ ρ : ℝ, 0 < ρ → ∀ z : ℂ,
      ρ / 100 ≤ infDist (0 : ℂ) (annulus z (ρ / 4) (2 * ρ)) →
      P {ω | annulusBallMassSize (μ ω) β ρ z /
        (μ ω) (annulus z (ρ / 4) (2 * ρ)) ∉
          Icc (ENNReal.ofReal C₂m) (ENNReal.ofReal C₂p)} ≤ δ := by
  obtain ⟨lo, hi, hlo, hhi, h⟩ :=
    exists_universal_wholePlane_ballMassSize_window hgrowth hγ hγ₂ hβ P₀ h₀ hμ₀ hδ
  let e : ℝ := -(γ * α)
  let K : ℝ := ((401 : ℝ) ^ |e|) ^ 2
  have hK : 0 < K := sq_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _)
  refine ⟨lo / K, K * hi, div_pos hlo hK, mul_pos hK hhi, ?_⟩
  intro Ω _ P hC hcirc μ hgff hμ hEx ρ hρ z hd
  have hQ : (0 : ℝ) < lqgQ γ := by unfold lqgQ; positivity
  obtain ⟨ν, hν⟩ := hEx hgff hγ hγ₂ hQ
  have hweight : ∀ᵐ ω ∂P, (μ ω).restrict {0}ᶜ =
      ((ν ω).withDensity fun x => ENNReal.ofReal (‖x‖ ^ e)).restrict {0}ᶜ := by
    have h1 : ∀ᵐ ω ∂P, IsLQGLimit γ (fieldCircleAverage α (hcirc ω)) (μ ω) := hμ
    filter_upwards [h1, lqgMeasureWeylScaling Ω P γ 0 hC hcirc hgff hγ hγ₂ hQ ν hν] with ω hω1 hω2
    exact restrict_compl_zero_eq_withDensity hω1 hω2
  have ht := size_window_failure_le_of_singular_weight P
    (β := β) (C₁m := lo) (C₁p := hi) (C₂m := 1) (C₂p := 1) hρ hd hweight
  exact ht.1.trans (h Ω P hC hcirc ν hgff hν ρ hρ z)

end HarmonicBalls.Section6
