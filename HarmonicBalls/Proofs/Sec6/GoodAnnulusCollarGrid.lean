import HarmonicBalls.Proofs.Sec6.RelativeCollarFieldLocality
import HarmonicBalls.Proofs.Sec6.GoodAnnulusUniformProbability

/-! # Joint good-annulus and relative-collar counts

The imported annulus iteration uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter
open scoped ENNReal
universe u

/-- Good annuli with controlled relative collars occur at the same radii,
with a polynomial lower-tail estimate uniform over deterministic centres. -/
theorem exists_goodAnnulus_relativeCollar_count_polynomial_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) {b : ℝ} (hb : 0 < b)
    (q β : ℝ) (hq : 0 < q)
    (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (d : ℝ≥0∞), 0 < d → ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (z : ℂ) (s : ℝ), 0 < s → ∀ ε : ℝ, 0 < ε →
        16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
        P {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
          (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
          IsGoodAnnulus (μ ω) (s*r) z a b ∧
          μ ω (annulus z (3*(s*r)-η*(s*r)) (5*(s*r)+η*(s*r)) \
            annulus z (3*(s*r)+η*(s*r)) (5*(s*r)-η*(s*r))) ≤
            d * μ ω (annulus z (3*(s*r)) (5*(s*r)))}.ncard : ℝ) <
          (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤ ENNReal.ofReal (C * ε ^ q) := by
  let : IsProbabilityMeasure P := h.isProbabilityMeasure
  have hlog : 0 < Real.log 7 := Real.log_pos (by norm_num)
  obtain ⟨p, hp, C, hCpos, hiter⟩ :=
    thick_annulus_subrange_probability (16 * Real.log 7 * q) β (by positivity) hβ
  have hp' : (1+p)/2 ∈ Ioo (0 : ℝ) 1 := by constructor <;> linarith [hp.1, hp.2]
  obtain ⟨a, ha, hprob⟩ := exists_universal_goodAnnulus_probability_all_radii
    hgrowth hγ hγ2 h hμ hb hp'
  refine ⟨a, ha, ?_⟩
  intro d hd
  have hδ : 0 < ENNReal.ofReal ((1-p)/2) := ENNReal.ofReal_pos.mpr (by linarith [hp.2])
  obtain ⟨η, hη, hη1, hcollar⟩ := exists_uniform_deterministicCentre_relative_collar
    hgrowth hγ hγ2 h hμ hAff hCC (c := 1) zero_lt_one hd hδ
  refine ⟨η, hη, hη1, C, hCpos, ?_⟩
  intro z s hs ε hε hlogε
  have hgff := hAff h 1 one_ne_zero z
  have hh := hiter Ω P (affinePairing hC hcirc 1 z) (affineCircle hcirc 1 z)
    hgff s hs (fun ω r => IsGoodAnnulus (μ ω) r z a b ∧
      μ ω (annulus z (3*r-η*r) (5*r+η*r) \
        annulus z (3*r+η*r) (5*r-η*r)) ≤ d * μ ω (annulus z (3*r) (5*r)))
    ?_ ?_ ε hε hlogε
  · have he : 16 * Real.log 7 * q / (16 * Real.log 7) = q := by field_simp
    simpa only [he] using hh
  · intro n
    have hr : 0 < s * (7 : ℝ)⁻¹ ^ n := by positivity
    obtain ⟨E, hE, he⟩ := isFieldMeasurableModConst_goodAnnulus_recentered_of_translation
      (lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth) h hμ hAff hγ hγ2 hr z ha.1 b
      (lqgMeasureNonatomic_of_volumeGrowth hgrowth P γ 0 _ _)
      (by intro v hv x hx hne; exact planarBrownianMotion_point_avoidance v x hne.symm)
    obtain ⟨F, hF, hf⟩ := isFieldMeasurableModConst_relativeCollarFailure_recentered
      (lqgMeasureFullSupportStmt_of_volumeGrowth hgrowth) h hμ hAff hCC hγ hγ2 hr hη1.le z d
    refine ⟨E ∩ Fᶜ, ?_, ?_⟩
    · apply MeasurableSet.inter _ hF.compl
      exact (fieldSigmaAlgebraModConst_mono 0 (affinePairing hC hcirc 1 z)
        (nearby_goodAnnulus_subset_thick_annulus hr (by simpa using (show (0 : ℝ) < _ by positivity)))) _ hE
    · filter_upwards [he, hf] with ω heω hfω
      simp only [Set.mem_inter_iff, Set.mem_compl_iff] at *
      exact propext (and_congr (iff_of_eq heω) (by simpa only [not_lt] using (iff_of_eq hfω).not))
  · intro n
    have hr : 0 < s * (7 : ℝ)⁻¹ ^ n := by positivity
    apply measure_ge_of_compl_le_ofReal P _ hp.1.le hp.2.le
    have hbound := (measure_mono (μ := P) (show
      {ω | ¬ (IsGoodAnnulus (μ ω) (s * (7 : ℝ)⁻¹ ^ n) z a b ∧
        μ ω (annulus z (3*(s*(7 : ℝ)⁻¹ ^ n)-η*(s*(7 : ℝ)⁻¹ ^ n))
          (5*(s*(7 : ℝ)⁻¹ ^ n)+η*(s*(7 : ℝ)⁻¹ ^ n)) \
          annulus z (3*(s*(7 : ℝ)⁻¹ ^ n)+η*(s*(7 : ℝ)⁻¹ ^ n))
          (5*(s*(7 : ℝ)⁻¹ ^ n)-η*(s*(7 : ℝ)⁻¹ ^ n))) ≤
          d * μ ω (annulus z (3*(s*(7 : ℝ)⁻¹ ^ n)) (5*(s*(7 : ℝ)⁻¹ ^ n))))} ⊆
      {ω | ¬ IsGoodAnnulus (μ ω) (s*(7 : ℝ)⁻¹ ^ n) z a b} ∪
      {ω | d * μ ω (annulus z (3*(s*(7 : ℝ)⁻¹ ^ n)) (5*(s*(7 : ℝ)⁻¹ ^ n))) <
        μ ω (annulus z (3*(s*(7 : ℝ)⁻¹ ^ n)-η*(s*(7 : ℝ)⁻¹ ^ n))
          (5*(s*(7 : ℝ)⁻¹ ^ n)+η*(s*(7 : ℝ)⁻¹ ^ n)) \
          annulus z (3*(s*(7 : ℝ)⁻¹ ^ n)+η*(s*(7 : ℝ)⁻¹ ^ n))
          (5*(s*(7 : ℝ)⁻¹ ^ n)-η*(s*(7 : ℝ)⁻¹ ^ n)))} by
        intro ω hω; simp only [mem_ofPred_eq, mem_union, not_and_or, not_le] at *; exact hω)).trans
      (measure_union_le (μ := P) _ _)
    have hsum := add_le_add (hprob Ω P hC hcirc μ h hμ _ hr z) (hcollar _ hr z).le
    have heq : 1 - (1+p)/2 = (1-p)/2 := by ring
    rw [heq, ← ENNReal.ofReal_add (by linarith [hp.2])] at hsum <;> try linarith [hp.2]
    have heq' : (1-p)/2 + (1-p)/2 = 1-p := by ring
    rw [heq'] at hsum
    exact hbound.trans hsum


/-- The joint count holds at every centre of the prescribed prevalence grid
with polynomially high probability, uniformly over the physical scale. -/
theorem exists_goodAnnulus_relativeCollar_prevalenceGrid
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) {b : ℝ} (hb : 0 < b)
    (β : ℝ) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∀ (d : ℝ≥0∞), 0 < d → ∃ η : ℝ, 0 < η ∧ η < 1 ∧ ∀ s : ℝ, 0 < s →
      PolyHighProb P (fun ε => {ω | ∀ z ∈ prevalenceGrid ε,
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ)) ≤
          ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
            (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
            IsGoodAnnulus (μ ω) (s*r) z a b ∧
            μ ω (annulus z (3*(s*r)-η*(s*r)) (5*(s*r)+η*(s*r)) \
              annulus z (3*(s*r)+η*(s*r)) (5*(s*r)-η*(s*r))) ≤
              d * μ ω (annulus z (3*(s*r)) (5*(s*r)))}.ncard : ℝ)}) := by
  obtain ⟨a, ha, hcount⟩ :=
    exists_goodAnnulus_relativeCollar_count_polynomial_tail
      hgrowth h hμ hAff hCC hγ hγ2 hb 6 β (by norm_num) hβ
  refine ⟨a, ha, ?_⟩
  intro d hd
  obtain ⟨η, hη, hη1, C, hC, htail⟩ := hcount d hd
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
