import HarmonicBalls.Draft.Section6
import HarmonicBalls.Proofs.Sec2.PolyHighProb

/-!
# A good annulus at each point of the prevalence grid

The quantitative count of good scales in Proposition 6.1 entails the
existence of a good scale at every grid point.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6

/-- The good-scale count is positive when the scale parameter is below one. -/
theorem exists_good_scale_of_prevalence_count {c ε : ℝ} (hc : 0 < c)
    (hε : 0 < ε) (hε1 : ε < 1) {P : ℝ → ℂ → Prop}
    (hcount : ∀ w ∈ prevalenceGrid ε,
      c * Real.log (ε ^ (-(1 / 2 : ℝ))) ≤
        ({ρ : ℝ | ρ ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧ P ρ w}.ncard : ℝ)) :
    ∀ w ∈ prevalenceGrid ε, ∃ ρ ∈ Icc ε (Real.sqrt ε), P ρ w := by
  have hlog : 0 < Real.log (ε ^ (-(1 / 2 : ℝ))) := by
    rw [Real.log_rpow hε]
    have hneg : Real.log ε < 0 := Real.log_neg hε hε1
    nlinarith
  intro w hw
  have hn := hcount w hw
  have hpos : (0 : ℝ) <
      ({ρ : ℝ | ρ ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧ P ρ w}.ncard : ℝ) :=
    (mul_pos hc hlog).trans_le hn
  have hne : {ρ : ℝ | ρ ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧ P ρ w}.Nonempty := by
    by_contra h
    have heq := Set.not_nonempty_iff_eq_empty.mp h
    rw [heq, Set.ncard_empty] at hpos
    norm_num at hpos
  obtain ⟨ρ, hρ, _, hP⟩ := hne
  exact ⟨ρ, hρ, hP⟩

end HarmonicBalls
