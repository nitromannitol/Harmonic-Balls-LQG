import HarmonicBalls.Proofs.Sec6.FixedCentreAnnulusCover

/-! # Scale-uniform finite covers by fixed-centre annuli

The probability estimate uses Leonardo Bonanno's proof in
`LatticeProb.Bonanno.LQGMetric.Papers.LM.L3_4M6`.
-/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set
open scoped ENNReal

/-- A single cardinal bound works for fixed-centre annulus covers at every
positive radius and every centre. -/
theorem exists_uniform_finite_cover_nearby_annuli :
    ∃ M : ℕ, ∀ (x : ℂ) (ρ : ℝ), 0 < ρ → ∃ T : Finset ℂ, T.card ≤ M ∧
      ∀ y ∈ ball x (ρ / 2), annulus y (ρ / 2) ρ ⊆ ⋃ z ∈ T, annulus z (ρ / 2) ρ := by
  obtain ⟨T, hT⟩ := exists_finite_cover_nearby_annuli (0 : ℂ) (ρ := 1) (by norm_num)
  refine ⟨T.card, ?_⟩
  intro x ρ hρ
  let f : ℂ → ℂ := fun z => ρ • z + x
  refine ⟨T.image f, Finset.card_image_le, ?_⟩
  have hdist (a b : ℂ) : dist (f a) (f b) = ρ * dist a b := by
    simp only [f, dist_add_right, dist_smul₀, Real.norm_eq_abs, abs_of_pos hρ]
  have hback (z : ℂ) : f (ρ⁻¹ • (z - x)) = z := by
    simp only [f, smul_inv_smul₀ hρ.ne', sub_add_cancel]
  have hdist0 (a : ℂ) : dist (f a) x = ρ * dist a 0 := by
    simpa only [f, smul_zero, zero_add] using hdist a 0
  intro y hy z hz
  let y' : ℂ := ρ⁻¹ • (y - x)
  let z' : ℂ := ρ⁻¹ • (z - x)
  have hy' : y' ∈ ball (0 : ℂ) ((1 : ℝ) / 2) := by
    have h : dist (f y') x < ρ / 2 := by simpa only [y', hback] using (mem_ball.mp hy)
    rw [hdist0] at h
    change dist y' 0 < (1 : ℝ) / 2
    nlinarith
  have hz' : z' ∈ annulus y' ((1 : ℝ) / 2) 1 := by
    have h : ρ / 2 < dist z y ∧ dist z y < ρ := by
      simpa only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le, and_comm] using hz
    have heq : dist z y = ρ * dist z' y' := by
      rw [← hback z, ← hback y, hdist]
    rw [heq] at h
    change dist z' y' < 1 ∧ ¬ dist z' y' ≤ (1 : ℝ) / 2
    constructor <;> nlinarith
  obtain ⟨t, ht, hzt⟩ := mem_iUnion₂.mp (hT y' hy' hz')
  refine mem_iUnion₂.mpr ⟨f t, Finset.mem_image.mpr ⟨t, ht, rfl⟩, ?_⟩
  have h : (1 : ℝ) / 2 < dist z' t ∧ dist z' t < 1 := by
    simpa only [annulus, mem_sdiff, mem_ball, mem_closedBall, not_le, and_comm] using hzt
  have heq : dist z (f t) = ρ * dist z' t := by
    rw [← hback z, hdist]
  change dist z (f t) < ρ ∧ ¬ dist z (f t) ≤ ρ / 2
  rw [heq]
  constructor <;> nlinarith


universe u

/-- A uniformly bounded cover of nearby-centre annuli has, with high
probability, criterion three simultaneously for every representative sequence
at every centre of the cover. -/
theorem exists_uniform_nearby_cover_representative_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ M : ℕ, ∃ a ∈ Ioo (0 : ℝ) 1, ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
    ∀ (s : ℝ), 0 < s → ∀ (x : ℂ) (F : ℕ → Finset ℂ),
      (∀ n, (F n).card ≤ 2 ^ (3 * n)) → (∀ n, (F n).Nonempty) →
    ∃ T : Finset ℂ, T.card ≤ M ∧
      (∀ y ∈ ball x (s / 2), annulus y (s / 2) s ⊆ ⋃ z ∈ T, annulus z (s / 2) s) ∧
      P {ω | ∃ z ∈ T, ∃ phase : ℕ → ℂ, (∀ n, phase n ∈ F n) ∧
        ¬ PhaseVeryGoodCriterionThree (μ ω) s z N a b (1 / 32) phase} ≤ δ := by
  obtain ⟨M, hcover⟩ := exists_uniform_finite_cover_nearby_annuli
  have hpos : 0 < δ / ((M : ℝ≥0∞) + 1) := ENNReal.div_pos hδ.ne' (by simp)
  obtain ⟨a, ha, N₀, hN₀, hbound⟩ :=
    exists_universal_growing_phaseCriterion_probability hgrowth hγ hγ₂ h₀ hμ₀ hb hpos
  refine ⟨M, a, ha, N₀, hN₀, ?_⟩
  intro N hN Ω _ P hC hcirc μ hgff hμ s hs x F hcard hF
  obtain ⟨T, hTcard, hTcover⟩ := hcover x s hs
  refine ⟨T, hTcard, hTcover, ?_⟩
  have h := measure_exists_bad_fixedCentre_phase_le P μ s N a b (1 / 32) F T hF
    (fun z _ => hbound N hN Ω P hC hcirc μ hgff hμ s hs z F hcard)
  calc
    _ ≤ (T.card : ℝ≥0∞) * (δ / ((M : ℝ≥0∞) + 1)) := h
    _ ≤ ((M : ℝ≥0∞) + 1) * (δ / ((M : ℝ≥0∞) + 1)) := by
      gcongr
      exact le_trans (Nat.cast_le.mpr hTcard) (le_add_right le_rfl)
    _ = δ := by rw [mul_comm, ENNReal.div_mul_cancel (by simp) (by simp)]


/-- The source counts needed for phase approximation, simultaneously over
representatives, lattice periods and small centre displacements. -/
def HasNearbyCentrePhaseCounts (μ : Measure ℂ) (s : ℝ) (x : ℂ) (N : ℕ)
    (a b c : ℝ) (F : ℕ → Finset ℂ) : Prop :=
  ∀ n, N ≤ n → ∀ q ∈ F n,
    ∀ t ∈ scaledLattice (dyadicScale n * s / 100), ∀ d : ℂ,
    dist 0 d < 2 * (dyadicScale (2 * n) * s / 100) →
    ∀ z ∈ annulus (x + d) (s / 2) s,
    z - (q + t) ∈ scaledLattice (dyadicScale n * s / 100) →
    c * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
      ({r : ℝ | r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s) ∧
        (∃ k : ℕ, 1 ≤ k ∧ r = s * (7 : ℝ)⁻¹ ^ k) ∧
        IsGoodAnnulus μ r z a b}.ncard : ℝ)

/-- Whole-plane source counts hold simultaneously at all nearby centres, with
constants uniform over centres, positive radii, and representative families. -/
theorem exists_universal_nearbyCentre_phaseCounts_probability
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
    ∀ (s : ℝ), 0 < s → ∀ (x : ℂ) (F : ℕ → Finset ℂ),
      (∀ n, (F n).card ≤ 2 ^ (3 * n)) → (∀ n, (F n).Nonempty) →
      P {ω | ¬ HasNearbyCentrePhaseCounts (μ ω) s x N a b (1 / 32) F} ≤ δ := by
  obtain ⟨M, a, ha, N₀, hN₀, hbound⟩ :=
    exists_uniform_nearby_cover_representative_probability hgrowth hγ hγ₂ h₀ hμ₀ hb hδ
  refine ⟨a, ha, N₀, hN₀, ?_⟩
  intro N hN Ω _ P hC hcirc μ hgff hμ s hs x F hcard hF
  obtain ⟨T, _, hcover, hprob⟩ :=
    hbound N hN Ω P hC hcirc μ hgff hμ s hs x F hcard hF
  apply (measure_mono ?_).trans hprob
  intro ω hbad
  by_contra hnot
  have hgood : ∀ y ∈ T, ∀ phase : ℕ → ℂ, (∀ n, phase n ∈ F n) →
      PhaseVeryGoodCriterionThree (μ ω) s y N a b (1 / 32) phase := by
    intro y hy phase hp
    by_contra hfail
    exact hnot ⟨y, hy, phase, hp, hfail⟩
  apply hbad
  intro n hn q hq t ht d hd z hz hlat
  have hdyad : dyadicScale (2 * n) ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hmul : dyadicScale (2 * n) * s ≤ s := by nlinarith
  have hd' : dist (x + d) x < s / 2 := by
    have heq : dist (x + d) x = dist 0 d := by simp [dist_eq_norm]
    rw [heq]
    linarith
  have hcounts : ∀ y ∈ T, ∀ n, N ≤ n → ∀ q ∈ F n,
      ∀ z ∈ annulus y (s / 2) s,
      z - q ∈ scaledLattice (dyadicScale n * s / 100) →
      (1 / 32 : ℝ) * Real.logb 7 (dyadicScale n ^ (-(1 / 2 : ℝ))) ≤
        ({r : ℝ | r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s) ∧
          (∃ k : ℕ, 1 ≤ k ∧ r = s * (7 : ℝ)⁻¹ ^ k) ∧
          IsGoodAnnulus (μ ω) r z a b}.ncard : ℝ) := by
    intro y hy
    exact representative_counts_of_all_phases (μ ω) s y N a b (1 / 32) F hF (hgood y hy)
  exact nearby_centre_counts_of_annulus_cover (μ ω) s N a b (1 / 32) F T hcounts
    (x + d) (hcover (x + d) hd') n hn q hq t ht z hz hlat


/-- Stability of tested good annuli under the displacement used to
approximate a lattice phase. -/
def HasNearbyGoodAnnulusTransfer (μ : Measure ℂ) (s : ℝ) (x : ℂ) (N : ℕ)
    (a b a' b' : ℝ) : Prop :=
  ∀ n, N ≤ n → ∀ z ∈ annulus x (s / 2) s, ∀ d : ℂ,
    dist 0 d < 2 * (dyadicScale (2 * n) * s / 100) →
    ∀ r ∈ Icc (dyadicScale n * s) (Real.sqrt (dyadicScale n) * s),
      IsGoodAnnulus μ r (z + d) a b → IsGoodAnnulus μ r z a' b'

/-- The failure of an arbitrary, possibly field-dependent phase criterion is
contained in the union of nearby-count and displacement-stability failures. -/
theorem measure_bad_phaseCriterion_le_nearby_failures
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    {s : ℝ} (hs : 0 < s) (x : ℂ) (N : ℕ) (a b a' b' c : ℝ)
    (F : ℕ → Finset ℂ)
    (hcover : ∀ n p, ∃ q ∈ F n, ∃ t ∈ scaledLattice (dyadicScale n * s / 100),
      ∃ d : ℂ, dist 0 d < 2 * (dyadicScale (2 * n) * s / 100) ∧ p + d = q + t)
    (phase : Ω → ℕ → ℂ) :
    P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) s x N a' b' c (phase ω)} ≤
      P {ω | ¬ HasNearbyCentrePhaseCounts (μ ω) s x N a b c F} +
        P {ω | ¬ HasNearbyGoodAnnulusTransfer (μ ω) s x N a b a' b'} := by
  classical
  calc
    _ ≤ P ({ω | ¬ HasNearbyCentrePhaseCounts (μ ω) s x N a b c F} ∪
      {ω | ¬ HasNearbyGoodAnnulusTransfer (μ ω) s x N a b a' b'}) := by
      apply measure_mono
      intro ω hbad
      by_contra h
      have hc : HasNearbyCentrePhaseCounts (μ ω) s x N a b c F := by
        by_contra hh
        exact h (Or.inl hh)
      have ht : HasNearbyGoodAnnulusTransfer (μ ω) s x N a b a' b' := by
        by_contra hh
        exact h (Or.inr hh)
      exact hbad (phaseVeryGoodCriterionThree_of_finite_phase_approximation hs x N
        a b a' b' c (phase ω) F hcover hc ht)
    _ ≤ _ := measure_union_le _ _

/-- The whole-plane arbitrary-phase failure probability is bounded by the
failure probability of small-displacement stability plus an arbitrarily small
error. No stability estimate is assumed or proved here. -/
theorem exists_universal_phaseCriterion_probability_le_stability_failure
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {γ : ℝ} (hγ : 0 < γ) (hγ₂ : γ < 2)
    {Ω₀ : Type u} [MeasurableSpace Ω₀] {P₀ : Measure Ω₀}
    {hC₀ : Ω₀ → (ℂ → ℝ) → ℝ} {hcirc₀ : Ω₀ → ℝ → ℂ → ℝ} {μ₀ : Ω₀ → Measure ℂ}
    (h₀ : IsWholePlaneGFF P₀ hC₀ hcirc₀) (hμ₀ : IsLQGMeasureOfField P₀ γ 0 hcirc₀ μ₀)
    {b : ℝ} (hb : 0 < b) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∀ N : ℕ, N₀ ≤ N →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ 0 hcirc μ →
    ∀ (s : ℝ), 0 < s → ∀ (x : ℂ) (a' b' : ℝ) (phase : Ω → ℕ → ℂ),
      P {ω | ¬ PhaseVeryGoodCriterionThree (μ ω) s x N a' b' (1 / 32) (phase ω)} ≤
        δ + P {ω | ¬ HasNearbyGoodAnnulusTransfer (μ ω) s x N a b a' b'} := by
  obtain ⟨a, ha, N₀, hN₀, hbound⟩ :=
    exists_universal_nearbyCentre_phaseCounts_probability hgrowth hγ hγ₂ h₀ hμ₀ hb hδ
  refine ⟨a, ha, N₀, hN₀, ?_⟩
  intro N hN Ω _ P hC hcirc μ hgff hμ s hs x a' b' phase
  obtain ⟨F, hcard, hcover⟩ := exists_dyadic_phase_displacement hs
  have hF : ∀ n, (F n).Nonempty := by
    intro n
    obtain ⟨q, hq, _⟩ := hcover n 0
    exact ⟨q, hq⟩
  calc
    _ ≤ P {ω | ¬ HasNearbyCentrePhaseCounts (μ ω) s x N a b (1 / 32) F} +
        P {ω | ¬ HasNearbyGoodAnnulusTransfer (μ ω) s x N a b a' b'} :=
      measure_bad_phaseCriterion_le_nearby_failures P μ hs x N a b a' b' (1 / 32) F hcover phase
    _ ≤ _ := add_le_add (hbound N hN Ω P hC hcirc μ hgff hμ s hs x F hcard hF) le_rfl

end HarmonicBalls.Section6
