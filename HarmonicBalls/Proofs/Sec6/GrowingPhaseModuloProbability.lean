import HarmonicBalls.Proofs.Sec6.GrowingPhaseProbability
import HarmonicBalls.Proofs.Sec8.PhasePeriodicity

/-! # Field-dependent phases modulo the dyadic lattice

The good-annulus count estimate uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

universe u

/-- A finite set of representatives at each mesh is enough: the actual
field-dependent phase may range over all lattice translates of those
representatives. No measurability of the choice of representatives is needed. -/
theorem exists_universal_singular_growing_phaseModulo_probability
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
      LQGMeasureExistence P γ 0 hC hcirc →
    ∀ (s : ℝ), 0 < s → ∀ x : ℂ,
      s / 100 ≤ infDist (0 : ℂ) (annulus x (s / 4) (2 * s)) →
    ∀ (F : ℕ → Finset ℂ), (∀ n, (F n).card ≤ 2 ^ (3 * n)) →
    ∀ (phase : Ω → ℕ → ℂ),
      (∀ ω n, ∃ q ∈ F n, phase ω n - q ∈ scaledLattice (dyadicScale n * s / 100)) →
      P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) s x N
        (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b (1 / 32) (phase ω)} ≤ δ := by
  classical
  obtain ⟨a, ha, N₀, hN₀, hbound⟩ :=
    exists_universal_singular_growing_phaseCriterion_probability
      (α := α) hgrowth hγ hγ₂ h₀ hμ₀ hb hδ
  refine ⟨a, ha, N₀, hN₀, ?_⟩
  intro N hN Ω _ P hC hcirc μ hgff hμ hE0 s hs x hd F hcard phase hphase
  choose q hq hshift using hphase
  have heq : {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) s x N
      (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b (1 / 32) (phase ω)} =
      {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) s x N
      (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b (1 / 32) (q ω)} := by
    ext ω
    have h := phaseVeryGoodCriterionThree_congr_lattice (μ ω) s x N
      (a / (((401 : ℝ) ^ |-(γ * α)|) ^ 2)) b (1 / 32) (q ω)
      (fun n => phase ω n - q ω n) (fun n _ => hshift ω n)
    simpa only [mem_ofPred_eq, add_sub_cancel] using h.not.symm
  rw [heq]
  exact hbound N hN Ω P hC hcirc μ hgff hμ hE0 s hs x hd F hcard q hq

end HarmonicBalls.Section6
