import HarmonicBalls.Proofs.Sec10.HoleExitTimeMass

/-! # Atoms of hole exit times

Before a compactly contained later cluster, the exit-time distribution of a
bounded initial hole has no atoms. No existence of holes is asserted. -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

universe u

/-- Under I2 and Lemma 8.2, the mass in a bounded initial hole whose exit time
is a prescribed later time vanishes whenever a still later closed cluster is
compactly contained in the unit disc. -/
theorem ae_cluster_holeExitTime_mass_singleton_eq_zero
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∀ c T : ℝ, t < c → c < T →
      closure (cluster (μ ω) 1 z T) ⊆ ball 0 1 →
      μ ω {x | x ∈ U ∧ holeExitTime (fun s => closure (cluster (μ ω) 1 z s)) x = c} = 0 := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_holeExitTime_interval_mass_le hI2 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hbound hmono
  intro t ht z hz U hU hUb c T htc hcT hclT
  apply le_antisymm _ bot_le
  apply ENNReal.le_of_forall_pos_le_add
  intro ε hε _
  let δ : ℝ := min ((c - t) / 2) (min ((T - c) / 2) ((ε : ℝ) / 4))
  have hδ : 0 < δ := by
    dsimp [δ]
    exact lt_min (by linarith) (lt_min (by linarith) (by exact div_pos (by exact_mod_cast hε) (by norm_num)))
  have hδt : δ ≤ (c - t) / 2 := min_le_left _ _
  have hδT : δ ≤ (T - c) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hδε : δ ≤ (ε : ℝ) / 4 := (min_le_right _ _).trans (min_le_right _ _)
  have ha : t ≤ c - δ := by linarith
  have hab : c - δ < c + δ := by linarith
  have hbT : c + δ ≤ T := by linarith
  have hclb : closure (cluster (μ ω) 1 z (c + δ)) ⊆ ball 0 1 :=
    (closure_mono (hmono (c + δ) T 1 (by linarith) hbT zero_lt_one z hz)).trans hclT
  have hle := hbound t ht z hz U hU hUb (c - δ) (c + δ) ha hab hclb
  calc
    μ ω {x | x ∈ U ∧ holeExitTime (fun s => closure (cluster (μ ω) 1 z s)) x = c} ≤
        μ ω {x | x ∈ U ∧ c - δ < holeExitTime (fun s => closure (cluster (μ ω) 1 z s)) x ∧
          holeExitTime (fun s => closure (cluster (μ ω) 1 z s)) x < c + δ} := by
            apply measure_mono
            intro x hx
            exact ⟨hx.1, by rw [hx.2]; linarith, by rw [hx.2]; linarith⟩
    _ ≤ ENNReal.ofReal ((c + δ) - (c - δ)) := hle
    _ ≤ 0 + (ε : ℝ≥0∞) := by
      simpa using ENNReal.ofReal_le_ofReal (show (c + δ) - (c - δ) ≤ (ε : ℝ) by linarith)

end HarmonicBalls
