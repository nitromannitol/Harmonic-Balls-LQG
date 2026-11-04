import HarmonicBalls.Draft.Section2
import HarmonicBalls.Draft.Section3
import HarmonicBalls.Draft.Section7
import HarmonicBalls.Draft.Section8
import HarmonicBalls.Proofs.Sec7.PrevalenceExistence
import HarmonicBalls.Proofs.Sec7.ContinuityScaleAssembly

/-!
# Right-continuity of clusters in the mass parameter

Proposition 7.2 follows from volume growth, the cluster properties, the
Harnack estimate, and zero boundary mass.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped Pointwise

universe u

/-- Proposition 7.2, conditional on the numbered results used in its proof. -/
theorem clusterTimeContinuity_of_steps
    (hvolume : LiouvilleVolumeGrowthStmt.{u}) (hconnected : ClusterOpenLaplacianStmt.{u})
    (hmonotone : ClusterMonotoneStmt.{u}) (hmass : ClusterConservationOfMassStmt.{u})
    (hHarnack : HarnackTypeEstimateStmt.{u}) (hboundary : BoundaryMeasureZeroOfCompactClusterStmt.{u}) :
    ClusterTimeContinuityStmt.{u} := by
  intro γ α₀ hγ hγ2 hα₀ β hβrange
  obtain ⟨c, hc, hHarnack⟩ := hHarnack
  obtain ⟨α, hα, hHarnack⟩ := hHarnack γ hγ hγ2
  have hβ : 0 < β := by
    have hnonneg : 0 ≤ (2 + γ) ^ 2 / 2 := by positivity
    have hmax := le_max_left ((2 + γ) ^ 2 / 2) (γ * (lqgQ γ - α₀))
    linarith
  refine ⟨140 * α ^ (-(4 * β)⁻¹), by positivity, ?_⟩
  intro Ω _ P hC hcirc μ hGFF hLQG
  obtain ⟨E, hE, hcount⟩ := hHarnack α₀ hα₀ Ω P hC hcirc μ hGFF hLQG
  let v : ℝ := min ((2 - γ) ^ 2 / 2) (γ * (lqgQ γ - α₀))
  have hv : 0 < v := by
    dsimp [v]
    exact lt_min (by positivity) (mul_pos hγ (sub_pos.mpr hα₀))
  let βplus : ℝ := v / 2
  have hβplus : 0 < βplus := by dsimp [βplus]; positivity
  have hβplus' : βplus < v := by dsimp [βplus]; linarith
  have hvol0 := (hvolume γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hLQG βplus β
    hβplus hβplus' hβrange).1
  have hvol : PolyHighProb P (fun s => {ω | ∀ x ∈ ball (0 : ℂ) 1,
      ENNReal.ofReal (s ^ β) ≤ μ ω (ball x s)}) := by
    apply hvol0.mono
    intro s ω hω x hx
    exact (hω x hx).1
  have hdyadic := ((hvol.comp_mul (c := (1 : ℝ) / 8) (by norm_num)).inter hcount).ae_eventually_dyadic
  filter_upwards [hdyadic, hconnected γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hLQG,
    hmonotone γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hLQG,
    hmass γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hLQG,
    hboundary γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hLQG] with ω hgood hconn hmono hm hb
  intro t ht z hz hcompact
  let A := cluster (μ ω) 1 z t
  have hAopen : IsOpen A := (hconn t 1 ht one_pos z hz).1
  have hAne : A.Nonempty := ⟨z, self_mem_cluster hz⟩
  have hAeq : μ ω A = ENNReal.ofReal t := (hm 1 t one_pos ht z hz).2.2 hcompact (hb t ht z hz hcompact)
  have hAfin : μ ω A ≠ ⊤ := by rw [hAeq]; exact ENNReal.ofReal_ne_top
  have hgood' : ∀ᶠ n : ℕ in atTop,
      (∀ x ∈ ball (0 : ℂ) 1,
        ENNReal.ofReal (((((2 : ℝ)⁻¹) ^ n) / 8) ^ β) ≤ μ ω (ball x ((((2 : ℝ)⁻¹) ^ n) / 8))) ∧
      (∀ w ∈ prevalenceGrid (((2 : ℝ)⁻¹) ^ n),
        ∃ ρ ∈ Icc (((2 : ℝ)⁻¹) ^ n) (Real.sqrt (((2 : ℝ)⁻¹) ^ n)), ω ∈ E ρ w) := by
    filter_upwards [hgood, eventually_ge_atTop 1] with n hn hn1
    have hs : 0 < ((2 : ℝ)⁻¹) ^ n := by positivity
    have hs1 : ((2 : ℝ)⁻¹) ^ n < 1 := by
      have hp := pow_le_pow_of_le_one (show (0 : ℝ) ≤ (2 : ℝ)⁻¹ by norm_num)
        (show (2 : ℝ)⁻¹ ≤ 1 by norm_num) hn1
      norm_num at hp ⊢
      linarith
    refine ⟨?_, exists_good_scale_of_prevalence_count hc hs hs1 hn.2⟩
    simpa only [mem_ofPred_eq, one_div, div_eq_mul_inv, one_mul, mul_comm] using hn.1
  apply eventually_contained_of_good_dyadic_scales (μ ω) hα hβ hAne hAopen.measurableSet.nullMeasurableSet
    hAfin hcompact (fun ρ w => ω ∈ E ρ w) hgood'
  · intro T hT
    have htT : 0 < t + T := by linarith
    refine ⟨hmono t (t + T) 1 ht (by linarith) one_pos z hz,
      (hconn (t + T) 1 htT one_pos z hz).2.1.isPreconnected, ?_⟩
    calc
      μ ω (cluster (μ ω) 1 z (t + T)) ≤ ENNReal.ofReal (t + T) := (hm 1 (t + T) one_pos htT z hz).1
      _ = μ ω A + ENNReal.ofReal T := by rw [hAeq, ENNReal.ofReal_add ht.le hT.le]
  · intro T hT w ρ hρ hEρ hdomain hsmall
    apply hE ω ρ hρ w hEρ z hz (t + T) (by linarith) _ hsmall
    intro y hy
    refine ⟨(hdomain hy).1, ?_⟩
    intro hyz
    exact (hdomain hy).2 (by simpa only [mem_singleton_iff] using hyz ▸ self_mem_cluster (μ := μ ω) (t := t) hz)

end HarmonicBalls
