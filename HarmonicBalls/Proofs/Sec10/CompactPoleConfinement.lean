import HarmonicBalls.Proofs.Sec7.UpperBoundReduction
import HarmonicBalls.Proofs.Sec7.ScaleConfinement
import HarmonicBalls.Proofs.Sec7.ClusterUpperBound
import HarmonicBalls.Proofs.Sec10.SmallMassCrossings
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Proofs.Sec6.HarnackType

/-!
# Small-mass confinement with a boundary margin

The origin-avoiding circle barrier works around any pole with enough room
inside the unit disk. The required margin is explicit.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6

universe u

/-- The Harnack circle cover for a pole whose distance from the unit boundary
exceeds the confinement radius. -/
theorem exists_origin_avoiding_lattice_circle_cover_of_margin
    {r ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hsmall : 10 * Real.sqrt ε + ε < r / 32) {z : ℂ} (hz : dist z 0 + r < 1)
    (P : ℝ → ℂ → Prop)
    (hgood : ∀ w ∈ prevalenceGrid ε, ∃ ρ ∈ Icc ε (Real.sqrt ε), P ρ w) :
    ∃ q : ℝ, r / 4 < q ∧ q < r / 2 ∧
      ∀ y ∈ sphere z q, ∃ w ∈ prevalenceGrid ε, ∃ ρ ∈ Icc ε (Real.sqrt ε),
        P ρ w ∧ y ∈ ball w (ρ / 2) ∧ closedBall w ρ ⊆ ball 0 1 \ {z} := by
  obtain ⟨q, hq₁, hqbound, hsep⟩ := exists_radius_separated_with_outer_margin hr (dist z 0)
  have hq₂ : q < r / 2 := by linarith
  refine ⟨q, hq₁, hq₂, fun y hy => ?_⟩
  have hyq : dist y z = q := mem_sphere.mp hy
  have hsqrt : 0 ≤ Real.sqrt ε := Real.sqrt_nonneg _
  have hyunit : dist y 0 < 1 := by
    have ht := dist_triangle y z (0 : ℂ)
    linarith
  have hyaway : r / 32 ≤ dist y 0 := by
    have ht := abs_dist_sub_le y (0 : ℂ) z
    rw [hyq, dist_comm (0 : ℂ) z] at ht
    exact hsep.trans ht
  obtain ⟨w, hw, hclose⟩ := exists_prevalenceGrid_dist_lt hε hyunit (by linarith)
  obtain ⟨ρ, hρ, hP⟩ := hgood w hw
  refine ⟨w, hw, ρ, hρ, hP, ?_, ?_⟩
  · rw [mem_ball]
    linarith [hρ.1]
  · apply closedBall_subset_unitBall_sdiff_pole_of_near_sphere hy (δ := ε / 50)
    · simpa only [dist_comm w y] using hclose
    · linarith [hρ.2]
    · linarith [hρ.2]

/-- A preconnected set with sufficiently small mass is confined to a ball
about its pole, uniformly while the pole retains the prescribed margin. -/
theorem closure_subset_ball_of_ball_volume_and_harnack_of_margin
    (μ : Measure ℂ) {B : Set ℂ} {r ε α T β : ℝ} {z : ℂ}
    (hr : 0 < r) (hε : 0 < ε)
    (hsmall : 10 * Real.sqrt ε + ε < r / 32) (hz : dist z 0 + r < 1)
    (hB : IsPreconnected B) (hzB : z ∈ B) (hα : 0 < α)
    (hmass : μ B ≤ ENNReal.ofReal T) (hT : T ≤ α * (ε / 8) ^ β)
    (hvol : ∀ x ∈ ball (0 : ℂ) 1,
      ENNReal.ofReal ((ε / 8) ^ β) ≤ μ (ball x (ε / 8)))
    (P : ℝ → ℂ → Prop)
    (hgood : ∀ w ∈ prevalenceGrid ε, ∃ ρ ∈ Icc ε (Real.sqrt ε), P ρ w)
    (hharnack : ∀ w ∈ prevalenceGrid ε, ∀ ρ ∈ Icc ε (Real.sqrt ε), P ρ w →
      closedBall w ρ ⊆ ball 0 1 \ {z} →
      μ (B ∩ annulus w (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) →
      B ∩ ball w (ρ / 2) = ∅) :
    closure B ⊆ ball z (r / 2) := by
  obtain ⟨q, hq₁, hq₂, hcover⟩ :=
    exists_origin_avoiding_lattice_circle_cover_of_margin hr hε hsmall hz P hgood
  apply closure_subset_ball_of_disjoint_sphere hB hzB (by linarith) hq₂
  apply Set.disjoint_left.mpr
  intro y hyB hyq
  obtain ⟨w, hw, ρ, hρ, hP, hyball, hdomain⟩ := hcover y hyq
  have hlower : μ B ≤ ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) := by
    calc
      μ B ≤ ENNReal.ofReal T := hmass
      _ ≤ ENNReal.ofReal (α * (ε / 8) ^ β) := ENNReal.ofReal_le_ofReal hT
      _ = ENNReal.ofReal α * ENNReal.ofReal ((ε / 8) ^ β) := ENNReal.ofReal_mul hα.le
      _ ≤ ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) := by
        gcongr
        exact lower_mass_half_annulus_of_ball_volume μ hε hvol hρ.1
          (hdomain.trans sdiff_subset)
  have hmass' : μ (B ∩ annulus w (ρ / 2) ρ) ≤ ENNReal.ofReal α * μ (annulus w (ρ / 2) ρ) :=
    (measure_mono inter_subset_left).trans hlower
  have hempty := hharnack w hw ρ hρ hP hdomain hmass'
  exact (eq_empty_iff_forall_notMem.mp hempty) y ⟨hyB, hyball⟩

/-- The high-probability confinement event holds uniformly for poles in any
fixed subdisc with the specified boundary margin. -/
theorem polyHighProb_cluster_confinement_at_scale_of_margin
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {μ : Ω → Measure ℂ}
    {α β c r b : ℝ} (hα : 0 < α) (hc : 0 < c) (hr : 0 < r) (hb : b + r < 1)
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
      ∀ z ∈ ball (0 : ℂ) b, closure (cluster (μ ω) 1 z t) ⊆ ball z (r / 2)}) := by
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
  have hzdist : dist z 0 < b := mem_ball.mp hz
  have hzmargin : dist z 0 + r < 1 := by linarith
  have hr1 : r < 1 := by linarith [dist_nonneg (x := z) (y := (0 : ℂ))]
  have hz1 : z ∈ ball (0 : ℂ) 1 := mem_ball.mpr (by linarith)
  have hprops := hω.2 t ht.1 z hz1
  have hvolε : ∀ x ∈ ball (0 : ℂ) 1,
      ENNReal.ofReal ((ε / 8) ^ β) ≤ μ ω (ball x (ε / 8)) := by
    simpa only [mem_ofPred_eq, one_div, div_eq_mul_inv, one_mul, mul_comm] using hω.1.1
  have hexists := exists_good_scale_of_prevalence_count hc hε hε1 hω.1.2
  apply closure_subset_ball_of_ball_volume_and_harnack_of_margin (μ ω) hr hε hsmall hzmargin hprops.1 (self_mem_cluster hz1) hα
    hprops.2 ht.2 hvolε (fun ρ w => ω ∈ E ρ w) hexists
  intro w _ ρ hρ hE hdomain hmass
  have hρ1 : ρ < 1 := lt_of_le_of_lt hρ.2 (by linarith)
  exact hharnack ω ρ ⟨lt_of_lt_of_le hε hρ.1, hρ1⟩ w hE z hz1 t ht.1 hdomain hmass


/-- The polynomial-probability small-mass confinement estimate for poles
in any fixed subdisc with positive distance from the boundary. -/
theorem cluster_confinement_polyHighProb_of_margin
    (hvolume : LiouvilleVolumeGrowthStmt.{u}) (hconnected : ClusterOpenLaplacianStmt.{u})
    (hmass : ClusterConservationOfMassStmt.{u}) (hHarnack : HarnackTypeEstimateStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ b r : ℝ, 0 < r → b + r < 1 →
      PolyHighProb P (fun T => {ω | ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) b,
        closure (cluster (μ ω) 1 z t) ⊆ ball z (r / 2)}) := by
  intro γ α₀ hγ hγ2 hα₀ Ω _ P hC hcirc μ hGFF hLQG b r hr hb
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
  have hscale := polyHighProb_cluster_confinement_at_scale_of_margin hα hc hr hb E
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


/-- Almost surely, small mass prevents crossings at any fixed positive scale,
uniformly for poles in a prescribed compact subdisc. -/
theorem ae_compact_poles_small_mass_crossings
    (hvolume : LiouvilleVolumeGrowthStmt.{u}) (hconnected : ClusterOpenLaplacianStmt.{u})
    (hmass : ClusterConservationOfMassStmt.{u}) (hHarnack : HarnackTypeEstimateStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ b r : ℝ, b < 1 → 0 < r → ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) b, ∀ w : ℂ, ∀ ρ : ℝ, r ≤ ρ →
        crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ) = ∅ := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  let d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hdpos : ∀ n, 0 < d n := by intro n; dsimp [d]; positivity
  have hcount : ∀ n : ℕ, ∀ᵐ ω ∂P, ∃ T : ℝ, 0 < T ∧
      ∀ t ∈ Ioc (0 : ℝ) T, ∀ z ∈ ball (0 : ℂ) (1 - d n),
        closure (cluster (μ ω) 1 z t) ⊆ ball z (d n / 4) := by
    intro n
    have hprob := cluster_confinement_polyHighProb_of_margin hvolume hconnected hmass hHarnack
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ (1 - d n) (d n / 2)
      (by positivity) (by linarith [hdpos n])
    filter_upwards [hprob.ae_eventually_dyadic] with ω hω
    obtain ⟨k, hk⟩ := hω.exists
    refine ⟨(2 : ℝ)⁻¹ ^ k, by positivity, ?_⟩
    intro t ht z hz
    have hrad : d n / 2 / 2 = d n / 4 := by ring
    simpa only [hrad] using (hk t ht z hz)
  filter_upwards [ae_all_iff.mpr hcount] with ω hω
  intro b r hb hr
  have hsmall : 0 < min (1 - b) r := lt_min (by linarith) hr
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hsmall
  have hden : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hdn : d n < min (1 - b) r := by
    dsimp [d]
    exact lt_of_le_of_lt (one_div_le_one_div_of_le hden (by linarith)) hn
  have hdb : d n < 1 - b := hdn.trans_le (min_le_left _ _)
  have hdr : d n < r := hdn.trans_le (min_le_right _ _)
  obtain ⟨T, hT, hbound⟩ := hω n
  refine ⟨T, hT, ?_⟩
  intro t ht z hz w ρ hρ
  have hz' : z ∈ ball (0 : ℂ) (1 - d n) := ball_subset_ball (by linarith) hz
  apply crossingComponents_eq_empty_of_closure_subset_ball hr hρ
  exact (hbound t ht z hz').trans (ball_subset_ball (by linarith))

/-- On any compact subdisc, the exact-radius crossing estimate holds for all
poles when the mass is sufficiently small at the prescribed scale. -/
theorem ae_compact_centers_crossings_for_small_mass
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (hvolume : LiouvilleVolumeGrowthStmt.{u}) (hconnected : ClusterOpenLaplacianStmt.{u})
    (hmass : ClusterConservationOfMassStmt.{u}) (hHarnack : HarnackTypeEstimateStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ b : ℝ, b < 1 → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ T : ℝ, 0 < T ∧
      ∀ w ∈ ball (0 : ℂ) b \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z : ℂ, ∀ t ∈ Ioc (0 : ℝ) T,
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ := by
  intro γ hγ hγ2
  obtain ⟨α, hα, hcross⟩ := ae_eventually_localized_crossings_exact_radius hI2 h6 γ hγ hγ2
  refine ⟨α, hα, ?_⟩
  intro α₀ hα₀ Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [hcross α₀ hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_compact_poles_small_mass_crossings hvolume hconnected hmass hHarnack
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hcross hsmall
  intro b hb
  let b' : ℝ := (b + 1) / 2
  have hbb' : b < b' := by dsimp [b']; linarith
  have hb' : b' < 1 := by dsimp [b']; linarith
  have hmargin : 0 < (b' - b) / 4 := by linarith
  filter_upwards [hcross, (eventually_lt_nhds (sq_pos_of_pos hmargin)).filter_mono nhdsWithin_le_nhds,
    (self_mem_nhdsWithin : Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ))] with ε hcross hε hεpos
  change 0 < ε at hεpos
  have hsqrt : Real.sqrt ε < (b' - b) / 4 := by
    have hs := Real.sqrt_lt_sqrt hεpos.le hε
    rw [Real.sqrt_sq_eq_abs, abs_of_pos hmargin] at hs
    exact hs
  obtain ⟨T, hT, hTbound⟩ := hsmall b' ε hb' hεpos
  refine ⟨T, hT, ?_⟩
  intro w hw
  have hw1 : w ∈ ball (0 : ℂ) 1 := (ball_subset_ball (by linarith)) hw.1
  obtain ⟨ρ, hρ, hρbound⟩ := hcross w ⟨hw1, hw.2⟩
  have hwsmall : dist w 0 < b := mem_ball.mp hw.1
  have hboundary : dist w 0 + 2 * ρ < 1 := by linarith [hρ.2]
  refine ⟨ρ, hρ, ?_⟩
  intro z t ht
  by_cases hz : z ∈ ball (0 : ℂ) b'
  · rw [hTbound t ht z hz w ρ hρ.1]
    simp
  · by_cases hz1 : z ∈ ball (0 : ℂ) 1
    · have hzfar : b' ≤ dist z 0 := le_of_not_gt (fun h => hz (mem_ball.mpr h))
      have hzw : 2 * ρ < dist z w := by
        have htri := dist_triangle z w (0 : ℂ)
        linarith [hρ.2]
      exact hρbound z hz1 t ht.1 hboundary hzw
    · rw [cluster_eq_empty_of_pole_not_mem hz1 ht.1.le]
      have hempty : crossingComponents ((∅ : Set ℂ) ∩ ball w (2 * ρ)) w (ρ / 3) (2 * ρ) = ∅ := by
        apply eq_empty_iff_forall_notMem.mpr
        intro C hC
        obtain ⟨x, hx, _⟩ := hC.1
        exact hx.1
      rw [hempty]
      simp

/-- The compact-centre small-mass crossing estimate using volume growth,
Lemma 2.4 and Proposition 6.2. -/
theorem ae_compact_centers_crossings_for_small_mass_of_volumeGrowth
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h6 : HarnackTypeComponentStmt.{u})
    (hvolume : LiouvilleVolumeGrowthStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∃ α ∈ Ioo (0 : ℝ) 1,
    ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ b : ℝ, b < 1 → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∃ T : ℝ, 0 < T ∧
      ∀ w ∈ ball (0 : ℂ) b \ ball 0 (20 * Real.sqrt ε),
      ∃ ρ ∈ Icc ε (Real.sqrt ε), ∀ z : ℂ, ∀ t ∈ Ioc (0 : ℝ) T,
        (crossingComponents (cluster (μ ω) 1 z t ∩ ball w (2 * ρ)) w (ρ / 3)
          (2 * ρ)).encard ≤ ⌈1 / α⌉₊ :=
  ae_compact_centers_crossings_for_small_mass hI2 h6 hvolume
    (clusterOpenLaplacian_proved hI2) (clusterConservationOfMass_proved hI2)
    (harnackTypeEstimateStmt_of_component h6)

end HarmonicBalls
