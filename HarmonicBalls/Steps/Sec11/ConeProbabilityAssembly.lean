import HarmonicBalls.Steps.Sec11.ConeSingularUniversal

/-! # Assembly of the cone-event probability estimate -/

namespace HarmonicBalls

/-! The cone-probability development uses Leonardo Bonanno's
Lattice-Probability formalization, including its Cameron-Martin port through
the local smooth-shift and fixed-shift decoder developments. -/

open MeasureTheory Metric Set Filter
open scoped ENNReal

universe u

/-- Lemma 11.8 from the scaled-ball mass, volume-growth and whole-plane
measure-existence inputs. -/
theorem coneBadEventProbability_of_existence
    (hS : WholePlaneScaledBallMassStep.{u}) (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    (hE : ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) (γ α : ℝ)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      LQGMeasureExistence P γ α hC hcirc) :
    ConeBadEventProbabilityStmt.{u} := by
  intro γ α hγ hγ2 hα Q hQ M hM
  classical
  by_cases hex : ∃ (Ω : Type u) (m : MeasurableSpace Ω) (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ),
      IsWholePlaneGFF P hC hcirc
  · obtain ⟨Ω₀, m₀, P₀, hC₀, hcirc₀, hG₀⟩ := hex
    let : MeasurableSpace Ω₀ := m₀
    have hE₀ := hE Ω₀ P₀ γ 0 hC₀ hcirc₀
    obtain ⟨μ₀, hμ₀⟩ := hE₀ hG₀ hγ hγ2 (by unfold lqgQ; positivity)
    obtain ⟨p, hp, hbound⟩ := cone_singular_universal_measurable_witness hS hgrowth
      hγ hγ2 hα hG₀ hE₀ hμ₀ Q hQ hM
    let q : ℝ≥0∞ := min p 1
    have hq : 0 < q := lt_min hp (by norm_num)
    have hqtop : q ≠ ∞ := ne_of_lt (lt_of_le_of_lt (min_le_right p 1) (by simp))
    have hqreal : 0 < q.toReal := ENNReal.toReal_pos hq.ne' hqtop
    let δ : ℝ := min 1 q.toReal / 2
    have hδpos : 0 < δ := by dsimp [δ]; positivity
    have hδone : δ < 1 := by dsimp [δ]; have := min_le_left (1 : ℝ) q.toReal; linarith
    have hδq : δ ≤ q.toReal := by
      dsimp [δ]; have := min_le_right (1 : ℝ) q.toReal; linarith
    have hδp : ENNReal.ofReal δ ≤ p := by
      calc
        ENNReal.ofReal δ ≤ ENNReal.ofReal q.toReal := ENNReal.ofReal_le_ofReal hδq
        _ = q := ENNReal.ofReal_toReal hqtop
        _ ≤ p := min_le_left p 1
    refine ⟨δ, ⟨hδpos, hδone⟩, ?_⟩
    intro Ω _ P hC hcirc μ hG hμ z
    refine ⟨0, ?_⟩
    intro n _ hd
    obtain ⟨A, hA, hAm, hAp⟩ := hbound P hC hcirc μ hG hμ
      (fun k => hE Ω P γ (lqgQ γ - 1 / ((k : ℝ) + 1)) hC hcirc) n z (le_of_lt hd)
    exact ⟨A, hA, hAm, hδp.trans hAp⟩
  · refine ⟨1 / 2, by norm_num, ?_⟩
    intro Ω _ P hC hcirc μ hG
    exact (hex ⟨Ω, inferInstance, P, hC, hcirc, hG⟩).elim

end HarmonicBalls
