import HarmonicBalls.Proofs.Sec10.HoleMassExtinctionTime

/-! # Continuity of remaining mass

Mass conservation controls the rate at which an increasing cluster absorbs
any finite-mass set. In particular the remaining mass of a hole is
one-Lipschitz while the cluster is compactly contained.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- A nested family with increments bounded in mass by elapsed time absorbs
any finite-mass set at a one-Lipschitz rate. -/
theorem lipschitzOnWith_remaining_measure_of_increment_bound
    (μ : Measure ℂ) {U : Set ℂ} (hU : μ U ≠ ∞)
    {C : ℝ → Set ℂ} {a b : ℝ}
    (hmono : ∀ s ∈ Icc a b, ∀ r ∈ Icc a b, s ≤ r → C s ⊆ C r)
    (hincr : ∀ s ∈ Icc a b, ∀ r ∈ Icc a b, s ≤ r →
      μ (C r \ C s) ≤ ENNReal.ofReal (r - s)) :
    LipschitzOnWith 1 (fun s => (μ (U \ C s)).toReal) (Icc a b) := by
  have hfin (s : ℝ) : μ (U \ C s) ≠ ∞ :=
    ne_top_of_le_ne_top hU (measure_mono sdiff_subset)
  have hpair (s : ℝ) (hs : s ∈ Icc a b) (r : ℝ) (hr : r ∈ Icc a b)
      (hsr : s ≤ r) :
      0 ≤ (μ (U \ C s)).toReal - (μ (U \ C r)).toReal ∧
      (μ (U \ C s)).toReal - (μ (U \ C r)).toReal ≤ r - s := by
    have hle : μ (U \ C r) ≤ μ (U \ C s) :=
      measure_mono (sdiff_subset_sdiff_right (hmono s hs r hr hsr))
    have hsplit : U \ C s ⊆ (U \ C r) ∪ (C r \ C s) := by
      intro x hx
      by_cases hxr : x ∈ C r
      · exact Or.inr ⟨hxr, hx.2⟩
      · exact Or.inl ⟨hx.1, hxr⟩
    have hbound : μ (U \ C s) ≤ μ (U \ C r) + ENNReal.ofReal (r - s) :=
      (measure_mono hsplit).trans ((measure_union_le _ _).trans
        (add_le_add le_rfl (hincr s hs r hr hsr)))
    have hreal := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨hfin r, ENNReal.ofReal_ne_top⟩) hbound
    rw [ENNReal.toReal_add (hfin r) ENNReal.ofReal_ne_top,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hsr)] at hreal
    have hrealmono := ENNReal.toReal_mono (hfin s) hle
    constructor <;> linarith
  apply LipschitzOnWith.of_dist_le_mul
  intro s hs r hr
  simp only [NNReal.coe_one, one_mul, Real.dist_eq]
  rcases le_total s r with hsr | hrs
  · obtain ⟨hlower, hupper⟩ := hpair s hs r hr hsr
    rw [abs_of_nonneg hlower, abs_of_nonpos (sub_nonpos.mpr hsr)]
    linarith
  · obtain ⟨hlower, hupper⟩ := hpair r hr s hs hrs
    rw [abs_of_nonpos (by linarith :
      (μ (U \ C s)).toReal - (μ (U \ C r)).toReal ≤ 0),
      abs_of_nonneg (sub_nonneg.mpr hrs)]
    linarith

universe u

/-- Under I2 and 8.2, the mass of any finite-mass set left outside the
cluster is one-Lipschitz over every positive interval ending at a compactly
contained cluster. The event is simultaneous over all choices of set, time,
and pole. -/
theorem ae_lipschitzOnWith_cluster_remaining_mass
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ a b : ℝ, 0 < a → a ≤ b → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z b) ⊆ ball 0 1 →
      ∀ U : Set ℂ, μ ω U ≠ ∞ →
        LipschitzOnWith 1 (fun s => (μ ω (U \ cluster (μ ω) 1 z s)).toReal)
          (Icc a b) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
      (clusterOpenLaplacian_proved hI2)
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω hopen hmono hmass hnull
  intro a b ha hab z hz hcl U hU
  apply lipschitzOnWith_remaining_measure_of_increment_bound (μ ω) hU
  · intro s hs r hr hsr
    exact hmono s r 1 (ha.trans_le hs.1) hsr zero_lt_one z hz
  · intro s hs r hr hsr
    have hspos : 0 < s := ha.trans_le hs.1
    have hrpos : 0 < r := hspos.trans_le hsr
    have hcls : closure (cluster (μ ω) 1 z s) ⊆ ball 0 1 :=
      (closure_mono (hmono s b 1 hspos hs.2 zero_lt_one z hz)).trans hcl
    have hfront : μ ω (frontier (cluster (μ ω) 1 z s)) = 0 := by
      apply measure_mono_null _ (hnull s hspos z hz)
      intro x hx
      exact ⟨hx, hcls (frontier_subset_closure hx)⟩
    have heq := (hmass 1 s zero_lt_one hspos z hz).2.2 hcls hfront
    exact measure_cluster_sdiff_le_of_mass_eq (μ ω) 1 z hspos.le hsr
      (hopen s 1 hspos zero_lt_one z hz).1
      (hmono s r 1 hspos hsr zero_lt_one z hz) heq
      (hmass 1 r zero_lt_one hrpos z hz).1

/-- For bounded sets, local finiteness supplies the finite-mass hypothesis.
This applies in particular to every bounded hole. -/
theorem ae_lipschitzOnWith_cluster_remaining_mass_of_bounded
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ a b : ℝ, 0 < a → a ≤ b → ∀ z ∈ ball (0 : ℂ) 1,
      closure (cluster (μ ω) 1 z b) ⊆ ball 0 1 →
      ∀ U : Set ℂ, Bornology.IsBounded U →
        LipschitzOnWith 1 (fun s => (μ ω (U \ cluster (μ ω) 1 z s)).toReal)
          (Icc a b) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_lipschitzOnWith_cluster_remaining_mass hI2 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ, hμ] with ω hlip hmeasure
  let : IsLocallyFiniteMeasure (μ ω) := hmeasure.isLocallyFiniteMeasure
  intro a b ha hab z hz hcl U hU
  apply hlip a b ha hab z hz hcl U
  exact ne_top_of_le_ne_top (hU.isCompact_closure.measure_lt_top (μ := μ ω)).ne
    (measure_mono subset_closure)

end HarmonicBalls
