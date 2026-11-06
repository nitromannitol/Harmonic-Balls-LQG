import HarmonicBalls.Proofs.Sec6.FineGridJointCounts
import HarmonicBalls.Proofs.Sec6.JointCollarNearbyCounts
import HarmonicBalls.Proofs.Sec6.PhaseGridApprox

/-! # Nearby-centre counts on finer grids

The fixed-centre estimate uses Leonardo Bonanno's annulus iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- With polynomially high probability, every finer-grid centre and
all centres within a fixed multiple of the smallest window radius share the
joint lower count, after explicit threshold losses. -/
theorem exists_nearby_goodAnnulus_fineGrid
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) {b : ℝ} (hb : 0 < b)
    (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧ ∀ c : ℝ, 0 < c → ∀ s : ℝ, 0 < s →
      PolyHighProb P (fun ε => {ω | ∀ z ∈ prevalenceGrid (c*ε), ∀ w : ℂ,
        dist w z < δ * (s*ε) →
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus (μ ω) (s*r) w (a/8) (b+1)}.ncard : ℝ)}) := by
  obtain ⟨a, ha, hgrid⟩ := exists_goodAnnulus_relativeCollar_fineGrid
    hgrowth h hμ hAff hCC hγ hγ2 hb β hβ
  have hd : 0 < ENNReal.ofReal (a/8) := ENNReal.ofReal_pos.mpr (div_pos ha.1 (by norm_num))
  obtain ⟨η, hη, hη1, hgrid⟩ := hgrid (ENNReal.ofReal (a/8)) hd
  obtain ⟨δ, hδ, htransfer⟩ := jointCollar_count_le_nearby_goodAnnulus_count hη
    (show 0 < ENNReal.ofReal (1/4 : ℝ) by positivity)
  have hbudget := goodAnnulus_collar_threshold_slack ha.1 ha.2 hb
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  have hreg : ∀ᵐ ω ∂P, ∀ (z : ℂ) (r : ℝ), 0 < r →
      0 < μ ω (annulus z (3*r) (5*r)) ∧ μ ω (annulus z (3*r) (5*r)) ≠ ∞ := by
    filter_upwards [lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth γ 0 hγ hγ2 hQ
      Ω P hC hcirc μ h hμ, hμ] with ω hfull hloc
    let : IsLocallyFiniteMeasure (μ ω) := hloc.isLocallyFiniteMeasure
    intro z r hr
    have hne : (annulus z (3*r) (5*r)).Nonempty := by
      refine ⟨z + (((4*r : ℝ) : ℂ)), ?_⟩
      have heq : dist (z + (((4*r : ℝ) : ℂ))) z = 4*r := by simp [dist_eq_norm, hr.le]
      change dist (z + (((4*r : ℝ) : ℂ))) z < 5*r ∧ ¬dist (z + (((4*r : ℝ) : ℂ))) z ≤ 3*r
      rw [heq]
      constructor <;> linarith
    exact ⟨hfull _ (isOpen_ball.sdiff isClosed_closedBall) hne,
      ne_top_of_le_ne_top measure_ball_ne_top (measure_mono sdiff_subset)⟩
  refine ⟨a, ha, δ, hδ, ?_⟩
  intro c hc s hs
  apply ((hgrid c hc s hs).inter_ae hreg).mono_of_small zero_lt_one
  intro ε hε hε1 ω hω z hz w hw
  let T : Set ℝ := {r | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧ ∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n}
  have hT : T.Finite := by
    refine finite_of_geometric (q := (7 : ℝ)⁻¹) (A := 1) (lo := ε)
      (by norm_num) (by norm_num) hε ?_
    intro r hr
    obtain ⟨hrange, n, hn⟩ := hr
    exact ⟨hrange.1, n, by simpa using hn⟩
  have hlo : ∀ r ∈ T, ε ≤ r := fun r hr => hr.1.1
  have hpos : ∀ r : ℝ, ε ≤ r → 0 < μ ω (annulus z (3*(s*r)) (5*(s*r))) :=
    fun r hr => (hω.2 z (s*r) (mul_pos hs (hε.trans_le hr))).1
  have hfin : ∀ r : ℝ, ε ≤ r → μ ω (annulus z (3*(s*r)) (5*(s*r))) ≠ ∞ :=
    fun r hr => (hω.2 z (s*r) (mul_pos hs (hε.trans_le hr))).2
  have hcount := htransfer (μ ω) s ε hs hε z w hw a (a/8) (a/2) b (b+1)
    (ENNReal.ofReal (a/8)) hpos hfin hbudget.1 hbudget.2.1 hbudget.2.2 T hT hlo
  apply (hω.1 z hz).trans
  simp only [T, Set.mem_ofPred_eq, and_assoc] at hcount
  exact_mod_cast hcount


/-- A point in the middle annulus is close to a point of the fine
prevalence grid, once the grid scale is sufficiently small. -/
theorem exists_prevalenceGrid_dist_lt {t : ℝ} (ht : 0 < t) (htsmall : t ≤ 1/10000)
    {w : ℂ} (hw : w ∈ annulus 0 (1/2) 1) :
    ∃ z ∈ prevalenceGrid t, dist w z < 2 * (t/100) := by
  obtain ⟨z, hz, hd⟩ := exists_scaledLattice_dist_lt w (show 0 < t/100 by positivity)
  have hwout : dist w 0 < 1 := hw.1
  have hwin : (1/2 : ℝ) < dist w 0 := lt_of_not_ge hw.2
  have hzout := dist_triangle z w 0
  have hzin := dist_triangle w z 0
  have hsym : dist z w = dist w z := dist_comm z w
  have hsqrt : Real.sqrt t ≤ 1/100 := by
    apply (Real.sqrt_le_left (by norm_num)).2
    nlinarith
  refine ⟨z, ⟨⟨?_, ?_⟩, hz⟩, hd⟩
  · change dist z 0 < 1+t
    linarith
  · change ¬dist z 0 < 10 * Real.sqrt t
    linarith

/-- The fine-grid count covers every point of the middle annulus, using a
mesh chosen after the displacement constant and physical scale. -/
theorem exists_all_middleAnnulus_goodAnnulus_counts
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) {b : ℝ} (hb : 0 < b)
    (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ s : ℝ, 0 < s →
      PolyHighProb P (fun ε => {ω | ∀ w ∈ annulus (0 : ℂ) (1/2) 1,
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus (μ ω) (s*r) w (a/8) (b+1)}.ncard : ℝ)}) := by
  obtain ⟨a, ha, δ, hδ, hgrid⟩ := exists_nearby_goodAnnulus_fineGrid
    hgrowth h hμ hAff hCC hγ hγ2 hb β hβ
  refine ⟨a, ha, ?_⟩
  intro s hs
  let c : ℝ := min 1 (25*δ*s)
  have hc : 0 < c := lt_min zero_lt_one (by positivity)
  have hcsmall : c ≤ 25*δ*s := min_le_right _ _
  apply (hgrid c hc s hs).mono_of_small (show 0 < 1/(10000*c) by positivity)
  intro ε hε hεsmall ω hω w hw
  have hsmall : c*ε ≤ 1/10000 := by
    have := (lt_div_iff₀ (show 0 < 10000*c by positivity)).1 hεsmall
    nlinarith
  obtain ⟨z, hz, hdist⟩ := exists_prevalenceGrid_dist_lt (mul_pos hc hε) hsmall hw
  apply hω z hz w
  apply hdist.trans_le
  have := mul_le_mul_of_nonneg_right hcsmall hε.le
  nlinarith

end HarmonicBalls.Section6
