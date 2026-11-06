import HarmonicBalls.Proofs.Sec6.FineGridSmallTolerance
import HarmonicBalls.Proofs.Sec6.JointCollarSameRadii

/-! # Common good-annulus radii near fine-grid centres

The fixed-centre estimate uses Leonardo Bonanno's annulus iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- With polynomially high probability, every finer-grid centre and
all centres within a fixed multiple of the smallest window radius share the
joint lower count at the same radii, after explicit threshold losses. -/
theorem exists_common_goodAnnulus_fineGrid_smallTolerance
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
            IsGoodAnnulus (μ ω) (s*r) z a (b/2) ∧
            IsGoodAnnulus (μ ω) (s*r) w (a/8) b}.ncard : ℝ)}) := by
  obtain ⟨a, ha, hgrid⟩ := exists_goodAnnulus_relativeCollar_fineGrid
    hgrowth h hμ hAff hCC hγ hγ2 (show 0 < b/2 by positivity) β hβ
  have hd : 0 < ENNReal.ofReal (a/8) := ENNReal.ofReal_pos.mpr (div_pos ha.1 (by norm_num))
  obtain ⟨η, hη, hη1, hgrid⟩ := hgrid (ENNReal.ofReal (a/8)) hd
  obtain ⟨δ, hδ, htransfer⟩ := jointCollar_count_le_common_goodAnnulus_count hη
    (show 0 < ENNReal.ofReal (b/12) from ENNReal.ofReal_pos.mpr (by positivity))
  have hslack := goodAnnulus_collar_threshold_slack ha.1 ha.2 hb
  have hbudget : ENNReal.ofReal (b/2) + 2 * ENNReal.ofReal (b/12) +
      ENNReal.ofReal (b/12) ≤ ENNReal.ofReal b := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_add (by positivity : 0 ≤ b/2) (by positivity : 0 ≤ 2*(b/12)),
      ← ENNReal.ofReal_add (by positivity : 0 ≤ b/2+2*(b/12)) (by positivity : 0 ≤ b/12)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
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
  have hcount := htransfer (μ ω) s ε hs hε z w hw a (a/8) (a/2) (b/2) b
    (ENNReal.ofReal (a/8)) hpos hfin hbudget hslack.2.1 hslack.2.2 T hT hlo
  apply (hω.1 z hz).trans
  simp only [T, Set.mem_ofPred_eq, and_assoc] at hcount
  exact_mod_cast hcount


end HarmonicBalls.Section6
