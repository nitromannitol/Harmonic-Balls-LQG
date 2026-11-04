import HarmonicBalls.Draft.Section7
import HarmonicBalls.Proofs.Sec7.PrevalenceExistence
import HarmonicBalls.Proofs.Sec7.UpperBoundReduction

/-!
# Cluster confinement at the annulus scale

The volume and prevalence events imply confinement simultaneously for every
centre and every mass below the annulus-scale threshold.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Section6

/-- The common good event confines all clusters whose mass parameter is at
most `α * (ε / 8)^β`. -/
theorem polyHighProb_cluster_confinement_at_scale
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    {α β c r : ℝ} (hα : 0 < α) (hc : 0 < c) (hr : 0 < r) (hr1 : r < 1)
    (E : ℝ → ℂ → Set Ω)
    (hvol : PolyHighProb P (fun s => {ω | ∀ x ∈ ball (0 : ℂ) 1,
      ENNReal.ofReal (s ^ β) ≤ μ ω (ball x s)}))
    (hcount : PolyHighProb P (fun ε => {ω | ∀ w ∈ prevalenceGrid ε,
      c * Real.log (ε ^ (-(1 / 2 : ℝ))) ≤
        ({ρ : ℝ | ρ ∈ Icc ε (Real.sqrt ε) ∧ (∃ n : ℕ, ρ = (8 : ℝ)⁻¹ ^ n) ∧ ω ∈ E ρ w}.ncard : ℝ)}))
    (hcluster : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      IsPreconnected (cluster (μ ω) 1 z t) ∧
      μ ω (cluster (μ ω) 1 z t) ≤ ENNReal.ofReal t)
    (hharnack : ∀ ω ρ, ρ ∈ Ioo (0 : ℝ) 1 → ∀ w, ω ∈ E ρ w →
      ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      closedBall w ρ ⊆ ball 0 1 \ {z} →
      μ ω (cluster (μ ω) 1 z t ∩ annulus w (ρ / 2) ρ) ≤
        ENNReal.ofReal α * μ ω (annulus w (ρ / 2) ρ) →
      cluster (μ ω) 1 z t ∩ ball w (ρ / 2) = ∅) :
    PolyHighProb P (fun ε => {ω | ∀ t ∈ Ioc (0 : ℝ) (α * (ε / 8) ^ β),
      ∀ z ∈ ball (0 : ℂ) (1 / 2), closure (cluster (μ ω) 1 z t) ⊆ ball z (r / 2)}) := by
  let δ : ℝ := min ((r / 400) ^ 2) (min (r / 400) 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hvol' := hvol.comp_mul (c := (1 : ℝ) / 8) (by norm_num)
  have hgood := (hvol'.inter hcount).inter_ae hcluster
  apply hgood.mono_of_small hδ
  intro ε hε hεδ ω hω t ht z hz
  have hεsq : ε < (r / 400) ^ 2 := hεδ.trans_le (min_le_left _ _)
  have hεr : ε < r / 400 := hεδ.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hε1 : ε < 1 := hεδ.trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hsqrt : Real.sqrt ε < r / 400 := (Real.sqrt_lt hε.le (by positivity)).2 hεsq
  have hsmall : 10 * Real.sqrt ε + ε < r / 32 := by linarith
  have hz1 : z ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball] at hz ⊢
    linarith
  have hprops := hω.2 t ht.1 z hz1
  have hvolε : ∀ x ∈ ball (0 : ℂ) 1,
      ENNReal.ofReal ((ε / 8) ^ β) ≤ μ ω (ball x (ε / 8)) := by
    simpa only [mem_ofPred_eq, one_div, div_eq_mul_inv, one_mul, mul_comm] using hω.1.1
  have hexists := exists_good_scale_of_prevalence_count hc hε hε1 hω.1.2
  apply closure_subset_ball_of_ball_volume_and_harnack (μ ω) hr hr1 hε hsmall
    (by simpa only [mem_ball, dist_comm] using hz) hprops.1 (self_mem_cluster hz1) hα
    hprops.2 ht.2 hvolε (fun ρ w => ω ∈ E ρ w) hexists
  intro w _ ρ hρ hE hdomain hmass
  have hρ1 : ρ < 1 := lt_of_le_of_lt hρ.2 (by linarith)
  exact hharnack ω ρ ⟨lt_of_lt_of_le hε hρ.1, hρ1⟩ w hE z hz1 t ht.1 hdomain hmass

end HarmonicBalls
