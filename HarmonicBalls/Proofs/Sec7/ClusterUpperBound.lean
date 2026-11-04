import HarmonicBalls.Draft.Section2
import HarmonicBalls.Draft.Section3
import HarmonicBalls.Proofs.Sec7.ScaleConfinement
import HarmonicBalls.Proofs.Sec7.ProbabilityScaling

/-!
# Small-mass cluster confinement

Proposition 7.1 follows from volume growth, connectedness and conservation of
mass for clusters, and the prevalence and Harnack estimate of Proposition 6.1.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6

universe u

/-- Proposition 7.1, conditional on the earlier numbered results used in its proof. -/
theorem clusterUpperBoundPolyHighProb_of_steps
    (hvolume : LiouvilleVolumeGrowthStmt.{u}) (hconnected : ClusterOpenLaplacianStmt.{u})
    (hmass : ClusterConservationOfMassStmt.{u}) (hHarnack : HarnackTypeEstimateStmt.{u}) :
    ClusterUpperBoundPolyHighProbStmt.{u} := by
  intro γ α₀ hγ hγ2 hα₀ Ω _ P hC hcirc μ hGFF hLQG r hr
  obtain ⟨c, hc, hHarnack⟩ := hHarnack
  obtain ⟨α, hα, hHarnack⟩ := hHarnack γ hγ hγ2
  obtain ⟨E, hE, hcount⟩ := hHarnack α₀ hα₀ Ω P hC hcirc μ hGFF hLQG
  let v : ℝ := min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀))
  have hv : 0 < v := by
    dsimp [v]
    exact lt_min (by positivity) (mul_pos hγ (sub_pos.mpr hα₀))
  let βplus : ℝ := v / 2
  let β : ℝ := max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) + 1
  have hβplus : 0 < βplus := by dsimp [βplus]; positivity
  have hβplus' : βplus < v := by dsimp [βplus]; linarith
  have hβ' : max ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀)) < β := by dsimp [β]; linarith
  have hβ : 0 < β := by
    have hnonneg : 0 ≤ (2 + γ) ^ 2 / 2 := by positivity
    have hmax := le_max_left ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀))
    linarith
  have hvol0 := (hvolume γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hLQG βplus β
    hβplus hβplus' hβ').1
  have hvol : PolyHighProb P (fun s => {ω | ∀ x ∈ ball (0 : ℂ) 1,
      ENNReal.ofReal (s ^ β) ≤ μ ω (ball x s)}) := by
    apply hvol0.mono
    intro s ω hω x hx
    exact (hω x hx).1
  have hcluster : ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      IsPreconnected (cluster (μ ω) 1 z t) ∧
      μ ω (cluster (μ ω) 1 z t) ≤ ENNReal.ofReal t := by
    filter_upwards [hconnected γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hLQG,
      hmass γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hLQG] with ω hconn hm t ht z hz
    exact ⟨(hconn t 1 ht one_pos z hz).2.1.isPreconnected, (hm 1 t one_pos ht z hz).1⟩
  have hscale := polyHighProb_cluster_confinement_at_scale hα hc hr.1 hr.2 E
    hvol hcount hcluster hE
  let a : ℝ := (2 * β)⁻¹
  have ha : 0 < a := by dsimp [a]; positivity
  have hscaled := (hscale.comp_mul (c := (8 : ℝ)) (by norm_num)).comp_rpow ha
  apply hscaled.mono_of_eventually
  filter_upwards [eventually_rpow_le_mul hα (show (1 / 2 : ℝ) < 1 by norm_num),
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with T hT hTpos
  intro ω hω t ht z hz
  apply hω t ⟨ht.1, ?_⟩ z hz
  have hsmall : T ≤ α * T ^ (1 / 2 : ℝ) := by simpa only [Real.rpow_one] using hT
  calc
    t ≤ T := ht.2
    _ ≤ α * T ^ (1 / 2 : ℝ) := hsmall
    _ = α * ((8 * T ^ a) / 8) ^ β := by
      have haβ : a * β = (1 / 2 : ℝ) := by dsimp [a]; field_simp
      rw [show (8 * T ^ a) / 8 = T ^ a by ring, ← Real.rpow_mul hTpos.le, haβ]

end HarmonicBalls
