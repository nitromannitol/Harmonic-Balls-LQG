import HarmonicBalls.Proofs.Sec6.ScaledSingularPhaseProbability
import HarmonicBalls.Proofs.Sec8.PhaseJointMeasurable
import HarmonicBalls.Proofs.Sec8.GoodEventPointPolarity

/-! # Independently sampled lattice phases

The good-annulus count estimate uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- A phase sampled independently of the field obeys the same singular-field
criterion-three bound as each deterministic phase. -/
theorem exists_universal_independent_phaseCriterion_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α hcirc μ →
      LQGMeasureExistence P γ 0 hC hcirc → Measurable μ →
      (∀ ω, IsLocallyFiniteMeasure (μ ω)) →
    ∀ (s : ℝ), 0 < s → ∀ x : ℂ,
      s / 100 ≤ infDist (0 : ℂ) (annulus x (s / 4) (2 * s)) →
    ∀ (T : Type u) [MeasurableSpace T] (Q : Measure T) [IsProbabilityMeasure Q]
      (phase : T → ℂ), Measurable phase →
      (Q.prod P) {p : T × Ω | ¬ PhaseVeryGoodCriterionThree (μ p.2) s x N
        (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b (1 / 32) (fun _ => phase p.1)} ≤ δ := by
  obtain ⟨a, ha, N₀, hN₀, hbound⟩ :=
    exists_universal_singular_phaseCriterion_probability_all_radii
      (α := α) hgrowth hγ hγ₂ h₀ hμ₀ hb hδ
  refine ⟨a, ha, N₀, hN₀, ?_⟩
  intro N hN Ω _ P hC hcirc μ hgff hμ hE0 hmeas hfinite s hs x hd T _ Q _ phase hphase
  let := hgff.isProbabilityMeasure
  have ha' : 0 < a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2) := div_pos ha.1 (sq_pos_of_pos (Real.rpow_pos_of_pos (by norm_num) _))
  have hunit := measurableSet_isGoodAnnulus_of_pos 1 (by norm_num) 0
    (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b ha'
  apply measure_prod_not_phaseVeryGoodCriterionThree_le P Q hmeas hfinite hphase s hs x N _ b
    (1 / 32) hunit
  intro q
  exact hbound N hN Ω P hC hcirc μ hgff hμ hE0 s hs x hd (fun _ => q)

end HarmonicBalls.Section6
