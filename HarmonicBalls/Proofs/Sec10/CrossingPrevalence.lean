import HarmonicBalls.Proofs.Sec10.CrossingLocalization
import HarmonicBalls.Proofs.Sec2.PolyHighProb

/-!
# Dyadic prevalence of good balls

The polynomial prevalence estimate supplies a good radius at every sufficiently
small dyadic scale, simultaneously at the points of the corresponding grid.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6

universe u

/-- The Borel-Cantelli step in Lemma 10.1: a positive logarithmic lower bound
on the number of good radii gives at least one good radius at each sufficiently
small dyadic scale. -/
theorem ae_eventually_dyadic_good_radius
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {c : ℝ} (hc : 0 < c)
    {E : ℝ → ℂ → Set Ω}
    (hprev : PolyHighProb P (fun ε => {ω | ∀ x₀ ∈ prevalenceGrid ε,
      c * Real.log (ε ^ (-(1 / 2 : ℝ))) ≤
        ({ρ : ℝ | ρ ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧
          ω ∈ E ρ x₀}.ncard : ℝ)})) :
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
      ∀ x₀ ∈ prevalenceGrid ((2 : ℝ)⁻¹ ^ k),
        ∃ ρ ∈ Icc ((2 : ℝ)⁻¹ ^ k) (Real.sqrt ((2 : ℝ)⁻¹ ^ k)),
          (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧ ω ∈ E ρ x₀ := by
  filter_upwards [hprev.ae_eventually_dyadic] with ω hω
  filter_upwards [hω, eventually_gt_atTop 0] with k hk hkpos
  intro x₀ hx₀
  let ε : ℝ := (2 : ℝ)⁻¹ ^ k
  have hεpos : 0 < ε := by dsimp [ε]; positivity
  have hεlt : ε < 1 := by
    dsimp [ε]
    exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hlog : 0 < Real.log (ε ^ (-(1 / 2 : ℝ))) := by
    rw [Real.log_rpow hεpos]
    exact mul_pos_of_neg_of_neg (by norm_num) (Real.log_neg hεpos hεlt)
  have hn := hk x₀ hx₀
  change c * Real.log (ε ^ (-(1 / 2 : ℝ))) ≤ _ at hn
  by_contra h
  have hempty : {ρ : ℝ | ρ ∈ Icc ε (Real.sqrt ε) ∧
      (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧ ω ∈ E ρ x₀} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro ρ hρ
    exact h ⟨ρ, hρ⟩
  rw [hempty] at hn
  simp only [ncard_empty, Nat.cast_zero] at hn
  exact (not_le_of_gt (mul_pos hc hlog)) hn

/-- At sufficiently small dyadic scales, every grid point has a radius for
which the localized crossing estimate holds simultaneously for all permitted
poles, masses, and nearby centres. -/
theorem ae_eventually_dyadic_localized_crossings
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α : ℝ, 0 < α ∧
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ᶠ k : ℕ in atTop,
      ∀ x₀ ∈ prevalenceGrid ((2 : ℝ)⁻¹ ^ k),
      ∃ ρ ∈ Icc ((2 : ℝ)⁻¹ ^ k) (Real.sqrt ((2 : ℝ)⁻¹ ^ k)),
        ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t → ∀ w : ℂ,
          dist w x₀ < ρ / 6 → dist w 0 + 2 * ρ < 1 → 2 * ρ < dist z w →
          (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
            (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  obtain ⟨c, hc, hcount⟩ := localizedCrossingCount_of_harnack hI2 h6
  intro γ hγ hγ2
  obtain ⟨α, hα, hcount⟩ := hcount γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  obtain ⟨E, hprev, hcount⟩ := hcount α₀ hα₀ Ω P hC hcirc μ hGFF hμ
  filter_upwards [ae_eventually_dyadic_good_radius hc hprev, hcount] with ω hgood hcount
  filter_upwards [hgood, eventually_gt_atTop 0] with k hk hkpos
  intro x₀ hx₀
  obtain ⟨ρ, hρ, _, hE⟩ := hk x₀ hx₀
  refine ⟨ρ, hρ, ?_⟩
  have hεpos : 0 < (2 : ℝ)⁻¹ ^ k := by positivity
  have hεlt : (2 : ℝ)⁻¹ ^ k < 1 :=
    pow_lt_one₀ (by norm_num) (by norm_num) (by omega)
  have hρpos : 0 < ρ := hεpos.trans_le hρ.1
  have hρlt : ρ < 1 := by
    have hsqrt : Real.sqrt ((2 : ℝ)⁻¹ ^ k) < 1 := by
      simpa using Real.sqrt_lt_sqrt hεpos.le hεlt
    exact hρ.2.trans_lt hsqrt
  exact hcount ρ ⟨hρpos, hρlt⟩ x₀ hE

end HarmonicBalls
