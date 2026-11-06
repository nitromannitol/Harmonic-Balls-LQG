import HarmonicBalls.Proofs.Sec6.GoodAnnulusCollarGrid
import HarmonicBalls.Proofs.Sec6.ScaleUniformRelativeCollar
import HarmonicBalls.Proofs.Sec6.Localization

/-! # Nearby-centre counts from joint annular collars

The grid estimate uses Leonardo Bonanno's annulus iteration in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- A joint good-annulus and collar count transfers to every centre within
one fixed fraction of the smallest radius in the tested window. -/
theorem jointCollar_count_le_nearby_goodAnnulus_count
    {η : ℝ} (hη : 0 < η) {e : ℝ≥0∞} (he : 0 < e) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ (μ : Measure ℂ) (s t : ℝ), 0 < s → 0 < t →
      ∀ z w : ℂ, dist w z < δ * (s*t) → ∀ a a' amid b b' : ℝ, ∀ d : ℝ≥0∞,
      (∀ r : ℝ, t ≤ r → 0 < μ (annulus z (3*(s*r)) (5*(s*r)))) →
      (∀ r : ℝ, t ≤ r → μ (annulus z (3*(s*r)) (5*(s*r))) ≠ ∞) →
      ENNReal.ofReal b + 2 * e + e ≤ ENNReal.ofReal b' →
      ENNReal.ofReal amid < ENNReal.ofReal a →
      ENNReal.ofReal a' + (ENNReal.ofReal a' + 1) * d ≤ ENNReal.ofReal amid →
      ∀ T : Set ℝ, T.Finite → (∀ r ∈ T, t ≤ r) →
      ({r : ℝ | r ∈ T ∧ IsGoodAnnulus μ (s*r) z a b ∧
        μ (annulus z (3*(s*r)-η*(s*r)) (5*(s*r)+η*(s*r)) \
          annulus z (3*(s*r)+η*(s*r)) (5*(s*r)-η*(s*r))) ≤
          d * μ (annulus z (3*(s*r)) (5*(s*r)))}).ncard ≤
      ({r : ℝ | r ∈ T ∧ IsGoodAnnulus μ (s*r) w a' b'}).ncard := by
  obtain ⟨δ, hδ, ht⟩ := exists_scale_uniform_goodAnnulus_of_relative_collar hη he
  refine ⟨δ, hδ, ?_⟩
  intro μ s t hs htpos z w hw a a' amid b b' d hpos hfin hbudget hmid hslack T hT hTlo
  apply Set.ncard_le_ncard ?_ (hT.subset (by intro r hr; exact hr.1))
  intro r hr
  have hrlo := hTlo r hr.1
  have hrpos : 0 < r := htpos.trans_le hrlo
  have hdist : dist w z < δ * (s*r) := by
    apply hw.trans_le
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrlo hs.le) hδ.le
  exact ⟨hr.1, ht μ (s*r) (mul_pos hs hrpos) z w hdist a a' amid b b' d
    (hpos r hrlo) (hfin r hrlo) hr.2.1 hbudget hmid hslack hr.2.2⟩


/-- For a positive mass threshold below one, concrete smaller thresholds
leave room for the relative collar comparison. -/
theorem goodAnnulus_collar_threshold_slack {a b : ℝ}
    (ha : 0 < a) (ha1 : a < 1) (hb : 0 < b) :
    ENNReal.ofReal b + 2 * ENNReal.ofReal (1/4 : ℝ) + ENNReal.ofReal (1/4 : ℝ) ≤
      ENNReal.ofReal (b+1) ∧
    ENNReal.ofReal (a/2) < ENNReal.ofReal a ∧
    ENNReal.ofReal (a/8) + (ENNReal.ofReal (a/8) + 1) * ENNReal.ofReal (a/8) ≤
      ENNReal.ofReal (a/2) := by
  constructor
  · rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by norm_num,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ← ENNReal.ofReal_add hb.le (by norm_num),
      ← ENNReal.ofReal_add (by linarith : 0 ≤ b+2*(1/4)) (by norm_num)]
    exact ENNReal.ofReal_le_ofReal (by linarith)
  constructor
  · exact (ENNReal.ofReal_lt_ofReal_iff ha).mpr (by linarith)
  · rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by norm_num,
      ← ENNReal.ofReal_add (by positivity : 0 ≤ a/8) (by norm_num),
      ← ENNReal.ofReal_mul (by positivity : 0 ≤ a/8+1),
      ← ENNReal.ofReal_add (by positivity : 0 ≤ a/8) (by positivity : 0 ≤ (a/8+1)*(a/8))]
    apply ENNReal.ofReal_le_ofReal
    nlinarith [sq_nonneg (a-1)]


/-- With polynomially high probability, every prescribed grid centre and
all centres within a fixed multiple of the smallest window radius share the
joint lower count, after explicit threshold losses. -/
theorem exists_nearby_goodAnnulus_prevalenceGrid
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) {b : ℝ} (hb : 0 < b)
    (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < s →
      PolyHighProb P (fun ε => {ω | ∀ z ∈ prevalenceGrid ε, ∀ w : ℂ,
        dist w z < δ * (s*ε) →
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus (μ ω) (s*r) w (a/8) (b+1)}.ncard : ℝ)}) := by
  obtain ⟨a, ha, hgrid⟩ := exists_goodAnnulus_relativeCollar_prevalenceGrid
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
  intro s hs
  apply ((hgrid s hs).inter_ae hreg).mono_of_small zero_lt_one
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

end HarmonicBalls.Section6
