import HarmonicBalls.Proofs.Sec6.RecenteredAnnularNormalizedRestriction
import HarmonicBalls.Proofs.Sec6.DeterministicCentreCollar
import HarmonicBalls.Proofs.Sec6.ThickAnnulusIteration
import HarmonicBalls.Proofs.Sec6.PrevalenceGridUnion

/-! # Field locality of relative annular collars

The imported annular locality uses Leonardo Bonanno's work in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- The relative collar event is unchanged by restriction to an annulus
which contains both its main annulus and its outer collar. -/
theorem relativeCollarFailure_restrict_two_six (μ : Measure ℂ) {r η : ℝ}
    (hr : 0 < r) (hη : η ≤ 1) (d : ℝ≥0∞) :
    RelativeCollarFailure (μ.restrict (annulus 0 (2*r) (6*r))) r η d ↔
      RelativeCollarFailure μ r η d := by
  have hmain : annulus (0 : ℂ) (3*r) (5*r) ⊆ annulus 0 (2*r) (6*r) := by
    intro x hx
    change dist x 0 < 5*r ∧ ¬dist x 0 ≤ 3*r at hx
    change dist x 0 < 6*r ∧ ¬dist x 0 ≤ 2*r
    constructor <;> linarith
  have houter : annulus (0 : ℂ) (3*r-η*r) (5*r+η*r) ⊆
      annulus 0 (2*r) (6*r) := by
    intro x hx
    change dist x 0 < 5*r+η*r ∧ ¬dist x 0 ≤ 3*r-η*r at hx
    change dist x 0 < 6*r ∧ ¬dist x 0 ≤ 2*r
    have hmul : η*r ≤ r := by nlinarith
    constructor <;> linarith
  have hU : MeasurableSet (annulus (0 : ℂ) (2*r) (6*r)) :=
    (isOpen_ball.sdiff isClosed_closedBall).measurableSet
  unfold RelativeCollarFailure
  rw [Measure.restrict_apply' hU, Measure.restrict_apply' hU,
    Set.inter_eq_left.mpr hmain, Set.inter_eq_left.mpr (sdiff_subset.trans houter)]

/-- At a deterministic centre the relative collar failure event is measurable
in the recentered whole-plane field on the surrounding annulus modulo constants. -/
theorem isFieldMeasurableModConst_relativeCollarFailure_recentered
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) {r η : ℝ} (hr : 0 < r) (hη : η ≤ 1)
    (z : ℂ) (d : ℝ≥0∞) :
    IsFieldMeasurableModConst P 0 (affinePairing hC hcirc 1 z)
      (annulus 0 (2*r) (6*r))
      {ω | d * μ ω (annulus z (3*r) (5*r)) <
        μ ω (annulus z (3*r-η*r) (5*r+η*r) \
          annulus z (3*r+η*r) (5*r-η*r))} := by
  obtain ⟨ν, hν, hνeq⟩ := exists_modConst_recentered_annular_normalizedRestriction
    hfull h hμ hAff hCC hγ hγ2 z (show 0 < 2*r by positivity) (by linarith : 2*r < 6*r)
  have hQ : 0 < lqgQ γ := by unfold lqgQ; positivity
  have hmass : ∀ᵐ ω ∂P,
      0 < ((μ ω).map (fun x : ℂ => x-z)) (annulus 0 (2*r) (6*r)) ∧
      ((μ ω).map (fun x : ℂ => x-z)) (annulus 0 (2*r) (6*r)) ≠ ∞ := by
    filter_upwards [hfull γ 0 hγ hγ2 hQ Ω P hC hcirc μ h hμ, hμ] with ω hf hloc
    let : IsLocallyFiniteMeasure (μ ω) := hloc.isLocallyFiniteMeasure
    rw [map_sub_annulus]
    have hne : (annulus z (2*r) (6*r)).Nonempty := by
      refine ⟨z + ((4*r : ℝ) : ℂ), ?_⟩
      have he : dist (z + ((4*r : ℝ) : ℂ)) z = 4*r := by simp [dist_eq_norm, hr.le]
      change dist (z + ((4*r : ℝ) : ℂ)) z < 6*r ∧ ¬dist (z + ((4*r : ℝ) : ℂ)) z ≤ 2*r
      rw [he]
      constructor <;> linarith
    exact ⟨hf _ (isOpen_ball.sdiff isClosed_closedBall) hne,
      ne_top_of_le_ne_top measure_ball_ne_top (measure_mono sdiff_subset)⟩
  refine ⟨ν ⁻¹' {m | RelativeCollarFailure m r η d}, hν (measurableSet_relativeCollarFailure r η d), ?_⟩
  filter_upwards [hνeq, hmass] with ω he hm
  change (d * μ ω (annulus z (3*r) (5*r)) < _) = RelativeCollarFailure (ν ω) r η d
  rw [he, normalizedRestriction, relativeCollarFailure_smul _ _ _ _ _
    (ENNReal.inv_ne_zero.mpr hm.2) (ENNReal.inv_ne_top.mpr hm.1.ne'),
    relativeCollarFailure_restrict_two_six _ hr hη,
    relativeCollarFailure_map_sub]

/-- At every deterministic centre, a single relative collar width yields an
arbitrarily high polynomial lower tail for the number of controlled collars
in each seven-adic window. The width is independent of the centre and scale. -/
theorem exists_deterministicCentre_relativeCollar_count_polynomial_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) {d : ℝ≥0∞} (hd : 0 < d)
    (q β : ℝ) (hq : 0 < q) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (z : ℂ) (s : ℝ), 0 < s → ∀ ε : ℝ, 0 < ε →
        16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
        P {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          μ ω (annulus z (3*(s*r)-η*(s*r)) (5*(s*r)+η*(s*r)) \
            annulus z (3*(s*r)+η*(s*r)) (5*(s*r)-η*(s*r))) ≤
            d * μ ω (annulus z (3*(s*r)) (5*(s*r)))}.ncard : ℝ) <
          (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤ ENNReal.ofReal (C * ε ^ q) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hlog : 0 < Real.log 7 := Real.log_pos (by norm_num)
  obtain ⟨p, hp, C, hCpos, hiter⟩ :=
    thick_annulus_subrange_probability (16 * Real.log 7 * q) β (by positivity) hβ
  have hδ : 0 < ENNReal.ofReal (1 - p) := ENNReal.ofReal_pos.mpr (by linarith [hp.2])
  obtain ⟨η, hη, hη1, hcollar⟩ := exists_uniform_deterministicCentre_relative_collar
    hgrowth hγ hγ2 h hμ hAff hCC (c := 1) zero_lt_one hd hδ
  refine ⟨η, hη, hη1, C, hCpos, ?_⟩
  intro z s hs ε hε hlogε
  have hgff := hAff h 1 one_ne_zero z
  have hh := hiter Ω P (affinePairing hC hcirc 1 z) (affineCircle hcirc 1 z)
    hgff s hs (fun ω r =>
      μ ω (annulus z (3*r-η*r) (5*r+η*r) \
        annulus z (3*r+η*r) (5*r-η*r)) ≤ d * μ ω (annulus z (3*r) (5*r)))
    ?_ ?_ ε hε hlogε
  · have he : 16 * Real.log 7 * q / (16 * Real.log 7) = q := by
      field_simp
    simpa only [he] using hh
  · intro n
    have hr : 0 < s * (7 : ℝ)⁻¹ ^ n := by positivity
    obtain ⟨E, hE, he⟩ := isFieldMeasurableModConst_relativeCollarFailure_recentered
      (lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth) h hμ hAff hCC hγ hγ2 hr hη1.le z d
    refine ⟨Eᶜ, hE.compl, ?_⟩
    filter_upwards [he] with ω heω
    simpa only [Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] using congrArg Not heω
  · intro n
    have hr : 0 < s * (7 : ℝ)⁻¹ ^ n := by positivity
    apply measure_ge_of_compl_le_ofReal P _ hp.1.le hp.2.le
    simpa only [Set.compl_ofPred, not_le] using (hcollar _ hr z).le

/-- Controlled relative collars are prevalent on the prescribed grid with
polynomially high probability. This concerns deterministic grid centres; it
does not assert an estimate at a root sampled from the LQG measure. -/
theorem exists_relativeCollar_prevalenceGrid
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) {d : ℝ≥0∞} (hd : 0 < d)
    (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ s : ℝ, 0 < s →
      PolyHighProb P (fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            μ ω (annulus z (3*(s*r)-η*(s*r)) (5*(s*r)+η*(s*r)) \
              annulus z (3*(s*r)+η*(s*r)) (5*(s*r)-η*(s*r))) ≤
              d * μ ω (annulus z (3*(s*r)) (5*(s*r)))}.ncard : ℝ)}) := by
  obtain ⟨η, hη, hη1, C, hC, htail⟩ :=
    exists_deterministicCentre_relativeCollar_count_polynomial_tail
      hgrowth h hμ hAff hCC hγ hγ2 hd 6 β (by norm_num) hβ
  obtain ⟨ε₀, hε₀, hlog⟩ := exists_radius_logb_inverse_ge (b := 7) (D := 16) (by norm_num)
  refine ⟨η, hη, hη1, ?_⟩
  intro s hs
  apply polyHighProb_forall_prevalenceGrid_of_fixed_center P _ (q := 6) (C := C)
    (by norm_num) hε₀
  intro ε hε hε₀' z hz
  convert htail z s hs ε hε (hlog ε hε hε₀') using 1
  congr 1
  ext ω
  change ¬ _ ↔ _
  exact not_le (α := ℝ)

end HarmonicBalls.Section6
