import HarmonicBalls.Proofs.Sec8.RandomMeasureContinuitySets
import HarmonicBalls.Proofs.Sec8.VagueMassConvergence
import HarmonicBalls.Proofs.Sec8.AEGermTriviality
import HarmonicBalls.Proofs.Sec8.AEPiSystemRatioRepresentatives
import HarmonicBalls.Proofs.Sec8.GoodEventMeasurablePositive
import HarmonicBalls.Proofs.Sec8.PositiveThresholdStationarity
import HarmonicBalls.Proofs.Sec8.LQGFrequencyFromRatios

/-! # Continuity-set exhaustions for LQG

Choose deterministic radii with almost surely null frontiers to exhaust a
reference ball strictly inside a given neighborhood.

The pointwise ergodic theorem used through `LQGFrequencyFromRatios` is from
Leonardo Bonanno’s LatticeProb formalization, `LatticeProb.Prob.Birkhoff`.
-/

open MeasureTheory Filter Set Metric
open scoped NNReal
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A strictly increasing sequence of radii converging to `R` exhausts the
open ball of radius `R`. -/
theorem iUnion_ball_of_tendsto_radius {X : Type*} [PseudoMetricSpace X]
    (z : X) (r : ℕ → ℝ) (R : ℝ) (hrlt : ∀ n, r n ≤ R)
    (hrlim : Tendsto r atTop (𝓝 R)) :
    (⋃ n, ball z (r n)) = ball z R := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_iUnion.mp hx
    exact mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hn) (hrlt n))
  · intro hx
    have hdist : dist x z < R := mem_ball.mp hx
    have ht : ∀ᶠ n in atTop, dist x z < r n := hrlim.eventually (Ioi_mem_nhds hdist)
    obtain ⟨n, hn⟩ := ht.exists
    exact mem_iUnion.mpr ⟨n, mem_ball.mpr hn⟩

/-- Each neighborhood contains a reference ball with an increasing
exhaustion by balls, all of whose frontiers have zero LQG mass almost surely. -/
theorem IsWholePlaneGFF.exists_ae_lqg_continuity_exhaustion
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R ∈ Ioo (0 : ℝ) ε, ∃ r : ℕ → ℝ,
      StrictMono r ∧ (∀ n, r n ∈ Ioo (0 : ℝ) R) ∧
      Tendsto r atTop (𝓝 R) ∧
      (⋃ n, ball (0 : ℂ) (r n)) = ball 0 R ∧
      ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (ball (0 : ℂ) (r n))) = 0) ∧
        μ ω (frontier (ball 0 R)) = 0 := by
  obtain ⟨q, hq, hzq⟩ := hGFF.exists_ae_lqg_null_frontier_balls_unbounded P hμ
    (fun _ => 0) (fun _ => 0) (fun _ => ε) (fun _ => hε)
  let R := q 0
  have hR : R ∈ Ioo (0 : ℝ) ε := hq 0
  obtain ⟨s, hsmono, hsrange, hslim⟩ := exists_seq_strictMono_tendsto' hR.1
  obtain ⟨r, hr, hzr⟩ := hGFF.exists_ae_lqg_null_frontier_balls_unbounded P hμ
    (fun _ => 0) s (fun n => s (n + 1)) (fun n => hsmono (Nat.lt_succ_self n))
  have hrmono : StrictMono r := by
    intro i j hij
    have hsle : s (i + 1) ≤ s j := hsmono.monotone (Nat.succ_le_of_lt hij)
    exact lt_trans (hr i).2 (lt_of_le_of_lt hsle (hr j).1)
  have hrrange (n : ℕ) : r n ∈ Ioo (0 : ℝ) R :=
    ⟨lt_trans (hsrange n).1 (hr n).1, lt_trans (hr n).2 (hsrange (n + 1)).2⟩
  have hrlim : Tendsto r atTop (𝓝 R) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le hslim tendsto_const_nhds
      (fun n => (hr n).1.le) (fun n => (hrrange n).2.le)
  refine ⟨R, hR, r, hrmono, hrrange, hrlim,
    iUnion_ball_of_tendsto_radius 0 r R (fun n => (hrrange n).2.le) hrlim, ?_⟩
  filter_upwards [hzr, hzq] with ω hzrω hzqω
  exact ⟨hzrω, hzqω 0⟩

/-- Emptying finitely many early balls preserves an increasing exhaustion and
leaves enough room for each circle average to stay in the larger ball. -/
theorem buffered_ball_exhaustion
    (r : ℕ → ℝ) (R ε : ℝ) (N : ℕ) (hrmono : Monotone r)
    (hrR : ∀ n, r n < R) (hRε : R < ε)
    (hN : dyadicScale N ≤ (ε - R) / 2)
    (hunion : (⋃ n, ball (0 : ℂ) (r n)) = ball 0 R) :
    let E : ℕ → Set ℂ := fun n => if n < N then ∅ else ball 0 (r n)
    Monotone E ∧ (⋃ n, E n) = ball 0 R ∧
      (∀ n z, z ∈ E n → closedBall z (dyadicScale n) ⊆ ball 0 ε) := by
  dsimp only
  let E : ℕ → Set ℂ := fun n => if n < N then ∅ else ball 0 (r n)
  change Monotone E ∧ (⋃ n, E n) = ball 0 R ∧ _
  have hEmono : Monotone E := by
    intro i j hij
    by_cases hi : i < N
    · simp [E, hi]
    · have hj : ¬ j < N := by omega
      simpa [E, hi, hj] using (ball_subset_ball (hrmono hij) :
        ball (0 : ℂ) (r i) ⊆ ball 0 (r j))
  refine ⟨hEmono, ?_, ?_⟩
  · rw [← hunion]
    ext z
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := mem_iUnion.mp hz
      by_cases h : n < N
      · simp [E, h] at hn
      · exact mem_iUnion.mpr ⟨n, by simpa [E, h] using hn⟩
    · intro hz
      obtain ⟨n, hn⟩ := mem_iUnion.mp hz
      refine mem_iUnion.mpr ⟨max n N, ?_⟩
      have hm : ¬ max n N < N := not_lt.mpr (le_max_right _ _)
      simp only [E, hm, ↓reduceIte]
      exact ball_subset_ball (hrmono (le_max_left n N)) hn
  · intro n z hz w hw
    by_cases hn : n < N
    · simp [hn] at hz
    · have hz' : dist z 0 < r n := by simpa [E, hn, mem_ball] using hz
      have hw' : dist w z ≤ dyadicScale n := mem_closedBall.mp hw
      have hdy : dyadicScale n ≤ dyadicScale N := dyadicScale_germ_cofinal.1 (le_of_not_gt hn)
      have htri := dist_triangle w z (0 : ℂ)
      rw [mem_ball]
      linarith [hrR n]

/-- A countable generating π-system and an interior buffered exhaustion can
be chosen so that all frontier hypotheses for normalized mass convergence
hold on a common almost-sure event. -/
theorem IsWholePlaneGFF.exists_ae_lqg_buffered_continuity_system
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (T : Set (Set ℂ)) (R : ℝ) (E : ℕ → Set ℂ),
      R ∈ Ioo (0 : ℝ) ε ∧ T.Countable ∧ IsPiSystem T ∧
      (∀ A ∈ T, IsOpen A) ∧
      (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom T ∧
      (∀ n, MeasurableSet (E n)) ∧ Monotone E ∧
      (⋃ n, E n) = ball 0 R ∧
      (∀ n z, z ∈ E n → closedBall z (dyadicScale n) ⊆ ball 0 ε) ∧
      ∀ᵐ ω ∂P, ∀ A ∈ T,
        (∀ n, μ ω (frontier (E n)) = 0 ∧ μ ω (frontier (A ∩ E n)) = 0) ∧
        μ ω (frontier (⋃ n, E n)) = 0 ∧ μ ω (frontier (A ∩ ⋃ n, E n)) = 0 := by
  obtain ⟨T, hcount, hpi, _, hopen, hgen, hTnull⟩ :=
    hGFF.exists_ae_lqg_continuity_piSystem P hμ
  obtain ⟨R, hR, r, hrmono, hrrange, _, hunion, hrnull⟩ :=
    hGFF.exists_ae_lqg_continuity_exhaustion P hμ hε
  obtain ⟨N, hN⟩ := dyadicScale_germ_cofinal.2 ((ε - R) / 2) (by linarith [hR.2])
  let E : ℕ → Set ℂ := fun n => if n < N then ∅ else ball 0 (r n)
  have ⟨hEmono, hEunion, hbuffer⟩ :=
    buffered_ball_exhaustion r R ε N hrmono.monotone (fun n => (hrrange n).2) hR.2 hN hunion
  have hEm (n : ℕ) : MeasurableSet (E n) := by
    dsimp [E]
    split_ifs
    · exact MeasurableSet.empty
    · exact isOpen_ball.measurableSet
  have hEnull : ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (E n)) = 0) ∧
      μ ω (frontier (⋃ n, E n)) = 0 := by
    filter_upwards [hrnull] with ω hω
    constructor
    · intro n
      by_cases hn : n < N
      · simp [E, hn]
      · simpa [E, hn] using hω.1 n
    · rw [hEunion]
      exact hω.2
  exact ⟨T, R, E, hR, hcount, hpi, hopen, hgen, hEm, hEmono, hEunion, hbuffer,
    ae_frontiers_intersections_of_common_continuity P μ E T hEnull hTnull⟩

/-- Local centered circle-average versions on a buffered exhaustion imply a
local version of the normalized LQG restriction to a smaller reference ball. -/
theorem IsWholePlaneGFF.exists_normalizedRestriction_of_centered_versions
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : @Measure Ω mΩ)
    [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : @IsWholePlaneGFF Ω mΩ P hC hcirc)
    (hμ : @IsLQGMeasureOfField Ω mΩ P γ α₀ hcirc μ)
    (hpositive : ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R →
      μ ω (ball 0 R) ≠ 0 ∧ μ ω (ball 0 R) ≠ ∞)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (R : ℝ) (E : ℕ → Set ℂ), R ∈ Ioo (0 : ℝ) ε ∧
      (⋃ n, E n) = ball 0 R ∧
      (∀ n z, z ∈ E n → closedBall z (dyadicScale n) ⊆ ball 0 ε) ∧
      ∀ d : ℕ → Ω → ℂ → ℝ,
        (∀ n, @Measurable (Ω × ℂ) ℝ (m.prod inferInstance) _
          (Function.uncurry (d n))) →
        (∀ n, ∀ᵐ ω ∂P, ∀ z ∈ E n,
          d n ω z = fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
            fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0) →
        ∃ ν : Ω → Measure ℂ, @Measurable Ω (Measure ℂ) m _ ν ∧
          ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 R) := by
  let : MeasurableSpace Ω := mΩ
  obtain ⟨T, R, E, hR, hcount, hpi, hopen, hgen, hEm, hmono, hEunion, hbuffer, hfront⟩ :=
    @IsWholePlaneGFF.exists_ae_lqg_buffered_continuity_system Ω mΩ P _ γ α₀
      hC hcirc μ hGFF hμ ε hε
  refine ⟨R, E, hR, hEunion, hbuffer, ?_⟩
  intro d hdm hdeq
  have hpos : ∀ᵐ ω ∂P, μ ω (ball 0 R) ≠ 0 ∧ μ ω (ball 0 R) ≠ ∞ :=
    hpositive.mono (fun _ h => h R hR.1)
  have hposE : ∀ᵐ ω ∂P, μ ω (⋃ n, E n) ≠ 0 ∧ μ ω (⋃ n, E n) ≠ ∞ := by
    simpa only [hEunion] using hpos
  have hbounded : Bornology.IsBounded (⋃ n, E n) := by
    rw [hEunion]
    exact Metric.isBounded_ball
  apply @exists_normalizedRestriction_version_of_ae_piSystem_ratios Ω mΩ P _ m hm
    μ (hGFF.aemeasurable_lqgMeasure hμ) (ball 0 R) isOpen_ball.measurableSet
    hpos T hcount hgen hpi (fun A hA => (hopen A hA).measurableSet)
  intro A hA
  have hfrontA : ∀ᵐ ω ∂P,
      (∀ n, μ ω (frontier (E n)) = 0 ∧ μ ω (frontier (A ∩ E n)) = 0) ∧
      μ ω (frontier (⋃ n, E n)) = 0 ∧ μ ω (frontier (A ∩ ⋃ n, E n)) = 0 :=
    hfront.mono (fun _ h => h A hA)
  obtain ⟨Y, hYm, hY⟩ := exists_local_lqg_ratio_version_of_centered_exhaustion
    P m hGFF hμ E hEm hmono hbounded A (hopen A hA).measurableSet hfrontA hposE 0 d hdm hdeq
  exact ⟨Y, hYm, by simpa only [hEunion] using hY⟩

open Classical in
/-- Local versions on arbitrarily small positive reference balls suffice for
local good-scale indicators; the representative may be measurable in the
sigma-algebra of a larger prescribed neighborhood. -/
theorem ae_local_veryGoodComparable_indicators_of_smaller_normalizedRestriction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (germ : ℝ → MeasurableSpace Ω) (μ : Ω → Measure ℂ) (β : ℝ) (N₀ : ℕ)
    (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (hpositive : ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R →
      μ ω (ball 0 R) ≠ 0 ∧ μ ω (ball 0 R) ≠ ∞)
    (hrep : ∀ ε, 0 < ε → ∃ R ∈ Ioo (0 : ℝ) ε, ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (germ ε) _ ν ∧
      ∀ᵐ ω ∂P, ν ω = normalizedRestriction (μ ω) (ball 0 R)) :
    ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → (fun ω =>
        if IsVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
          AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0) =ᵐ[P] Y n) := by
  intro ε hε
  obtain ⟨R, hR, ν, hν, heq⟩ := hrep ε hε
  obtain ⟨K, hK⟩ := eventually_ball_six_dyadic_subset (0 : ℂ) hR.1
  refine ⟨K, ?_⟩
  apply @ae_local_veryGoodComparable_indicators_of_local_measure Ω mΩ P (germ ε)
    μ ν β 0 N₀ a b C₁m C₁p C₂m C₂p C₃ m K (ball 0 R) hν hK
  · intro n
    exact measurableSet_isVeryGoodAnnulus_zero_of_unit_good β (dyadicScale n)
      (dyadicScale_pos n) N₀ a b C₁m C₁p C₂m C₂p C₃ hunit
  · filter_upwards [heq, hpositive] with ω hω hp
    refine ⟨μ ω (ball 0 R), (hp R hR.1).1, (hp R hR.1).2, ?_⟩
    rw [hω]
    exact restrict_eq_smul_normalizedRestriction (μ ω) isOpen_ball.measurableSet
      (hp R hR.1).1 (hp R hR.1).2

open Classical in
/-- Jointly measurable local centered circle averages yield germ-local
versions of the good-scale indicators. -/
theorem IsWholePlaneGFF.ae_local_indicators_of_centered_circle_versions
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : @Measure Ω mΩ)
    [IsProbabilityMeasure P] (germ : ℝ → MeasurableSpace Ω)
    (hgerm : ∀ ε, 0 < ε → germ ε ≤ mΩ)
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : @IsWholePlaneGFF Ω mΩ P hC hcirc)
    (hμ : @IsLQGMeasureOfField Ω mΩ P γ α₀ hcirc μ)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ)
    (hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b})
    (hpositive : ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R →
      μ ω (ball 0 R) ≠ 0 ∧ μ ω (ball 0 R) ≠ ∞)
    (hcenter : ∀ ε, 0 < ε → ∀ n, ∃ d : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ ((germ ε).prod inferInstance) _ (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ z, closedBall z (dyadicScale n) ⊆ ball 0 ε →
        d ω z = fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
          fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0) :
    ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ (germ ε) _ (Y n)) ∧
      (∀ n, K ≤ n → (fun ω =>
        if IsVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
          AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0) =ᵐ[P] Y n) := by
  let : MeasurableSpace Ω := mΩ
  apply ae_local_veryGoodComparable_indicators_of_smaller_normalizedRestriction
    P germ μ β N₀ a b C₁m C₁p C₂m C₂p C₃ m hunit hpositive
  intro ε hε
  obtain ⟨R, E, hR, _, hbuffer, hbuild⟩ :=
    @IsWholePlaneGFF.exists_normalizedRestriction_of_centered_versions Ω mΩ P _
      (germ ε) (hgerm ε hε) γ α₀ hC hcirc μ hGFF hμ hpositive ε hε
  choose d hdmeas hdeq using hcenter ε hε
  have hdeqE (n : ℕ) : ∀ᵐ ω ∂P, ∀ z ∈ E n,
      d n ω z = fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
        fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0 := by
    filter_upwards [hdeq n] with ω hω z hz
    exact hω z (hbuffer n z hz)
  obtain ⟨ν, hν, heq⟩ := hbuild d hdmeas hdeqE
  exact ⟨R, hR, ν, hν, heq⟩

universe u

open Classical MarkovProcess in
/-- Centered circle-average versions give the field-germ local indicators
needed in the good-scale frequency argument. -/
theorem IsWholePlaneGFF.ae_field_germ_indicators_of_centered_circle_versions
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m : ℝ) (ha : 0 < a)
    (hpolar : ∀ u ∈ sphere (0 : ℂ) 4, ∀ x ∈ annulus (0 : ℂ) 3 5, x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (hcenter : ∀ ε, 0 < ε → ∀ n, ∃ d : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ
        ((Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)).prod inferInstance) _
        (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ z, closedBall z (dyadicScale n) ⊆ ball 0 ε →
        d ω z = fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
          fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0) :
    ∀ ε, 0 < ε → ∃ K, ∃ Y : ℕ → Ω → ℝ,
      (∀ n, K ≤ n → @Measurable Ω ℝ
        (Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)) _ (Y n)) ∧
      (∀ n, K ≤ n → (fun ω =>
        if IsVeryGoodAnnulus (μ ω) β (dyadicScale n) 0 N₀ a b C₁m C₁p C₂m C₂p C₃ ∧
          AnnulusBallComparison (μ ω) n 0 m then (1 : ℝ) else 0) =ᵐ[P] Y n) := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  have hfullae := hfull γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hμ] with ω hω
    exact hω.isLocallyFiniteMeasure
  have hunit : MeasurableSet {ν : Measure ℂ | IsGoodAnnulus ν 1 0 a b} := by
    apply measurableSet_isGoodAnnulus_of_ae_point_avoidance 1 (by norm_num) 0 a b ha
    simpa using hpolar
  apply hGFF.ae_local_indicators_of_centered_circle_versions P
    (fun ε => Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)) _ hμ
    β N₀ a b C₁m C₁p C₂m C₂p C₃ m hunit
    (ae_referenceBall_pos_finite P μ hfullae hloc) hcenter
  intro ε hε
  exact (Section6.fieldSigmaAlgebraModConst_le α₀ hC _).trans
    (hGFF.fieldSigmaAlgebra_le α₀ _)

open Classical MarkovProcess in
/-- The origin good-scale frequency follows from centered circle-average
versions, field-germ triviality, point avoidance, and the stated LQG inputs. -/
theorem ae_eventually_goodScaleCount_of_centered_circle_versions
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ ε₀ : ℝ) (ha : 0 < a)
    (hpolar : ∀ u ∈ sphere (0 : ℂ) 4, ∀ x ∈ annulus (0 : ℂ) 3 5, x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x)
    (hcenter : ∀ ε, 0 < ε → ∀ n, ∃ d : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ
        ((Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)).prod inferInstance) _
        (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ z, closedBall z (dyadicScale n) ⊆ ball 0 ε →
        d ω z = fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
          fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0)
    (htrivial : ∀ A : Set Ω, (∀ ε, 0 < ε →
      MeasurableSet[Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)] A) →
      P A = 0 ∨ P A = 1)
    (hε : 0 ≤ ε₀) (hεζ : ε₀ < ζ)
    (hfail : P {ω | ¬ (IsVeryGoodAnnulus (μ ω) β (dyadicScale 0) 0 N₀
      a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) 0 0 m)} ≤ ENNReal.ofReal ε₀) :
    ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop, (1 - ζ) * (N : ℝ) ≤
      veryGoodComparableScaleCount (μ ω) β 0 N₀ a b C₁m C₁p C₂m C₂p C₃ m N := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let A : Set Ω := {ω | IsVeryGoodAnnulus (μ ω) β (dyadicScale 0) 0 N₀
    a b C₁m C₁p C₂m C₂p C₃ ∧ AnnulusBallComparison (μ ω) 0 0 m}
  have hd := identDistrib_lqg_veryGoodComparable_of_unit_point_avoidance hγ hγ2 hα
    hGFF hμ hAff hCC β N₀ a b C₁m C₁p C₂m C₂p C₃ m ha hpolar
  have hF := (measurable_pi_apply (0 : ℕ)).comp_aemeasurable hd.aemeasurable_fst
  have hAn : NullMeasurableSet A P := by
    convert hF.nullMeasurableSet_preimage (measurableSet_singleton (1 : ℝ)) using 1
    ext ω
    simp only [A, Set.mem_ofPred_eq, Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply]
    split_ifs <;> simp_all
  have hq : 1 - ζ < (P A).toReal := probability_gt_of_small_failure P A hAn hε hεζ hfail
  have hlocal := hGFF.ae_field_germ_indicators_of_centered_circle_versions
    hfull hγ hγ2 hα hμ β N₀ a b C₁m C₁p C₂m C₂p C₃ m ha hpolar hcenter
  apply ae_eventually_veryGoodComparableScaleCount_of_identDistrib P μ β 0 N₀
    a b C₁m C₁p C₂m C₂p C₃ m ζ
    (fun ε => Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)) dyadicScale
    dyadicScale_pos dyadicScale_germ_cofinal.2 dyadicScale_germ_cofinal.1
    (monotone_fieldSigmaAlgebraModConst_ball α₀ hC 0) hlocal htrivial
  · simpa only [Nat.add_comm] using hd
  · exact hq

open Classical MarkovProcess in
/-- Uniform origin good-scale parameters, conditional on local centered
circle-average versions and triviality of the field germ. -/
theorem origin_many_good_scales_of_centered_circle_versions
    (hVG : VeryGoodAnnulusProbabilityStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    (hpolar : ∀ u ∈ sphere (0 : ℂ) 4, ∀ x ∈ annulus (0 : ℂ) 3 5, x ≠ u →
      ∀ᵐ p ∂(planarBrownianMotion u), ∀ t : ℝ≥0, p t ≠ x) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ β : ℝ, (2 + γ) ^ 2 / 2 < β →
    ∃ C₃ : ℝ, 0 < C₃ ∧ ∀ ζ : ℝ, 0 < ζ → ∀ b ∈ Ioo (0 : ℝ) 1,
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
    ∃ N₁ : ℕ, 1 ≤ N₁ ∧ ∀ N₀ : ℕ, N₁ ≤ N₀ → ∃ m : ℝ, 0 < m ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
      IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
      WholePlaneGFFAffineInvariance P hC hcirc → LQGMeasureCoordChange P γ α₀ hC hcirc →
      (∀ ε, 0 < ε → ∀ n, ∃ d : Ω → ℂ → ℝ,
        @Measurable (Ω × ℂ) ℝ
          ((Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)).prod inferInstance) _
          (Function.uncurry d) ∧
        ∀ᵐ ω ∂P, ∀ z, closedBall z (dyadicScale n) ⊆ ball 0 ε →
          d ω z = fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
            fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0) →
      (∀ A : Set Ω, (∀ ε, 0 < ε →
        MeasurableSet[Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)] A) →
        P A = 0 ∨ P A = 1) →
      ∀ᵐ ω ∂P, ∀ᶠ N : ℕ in atTop,
        (1 - ζ) * (N : ℝ) ≤ veryGoodComparableScaleCount (μ ω) β 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ m N := by
  obtain ⟨C₃, hC₃, hp⟩ := exists_joint_goodScale_parameters hVG hfull
  intro γ α₀ hγ hγ2 hα β hβ
  refine ⟨C₃, hC₃, ?_⟩
  intro ζ hζ b hb
  let δ : ℝ := min (ζ / 2) (1 / 2)
  have hδ : δ ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · exact lt_min (by linarith) (by norm_num)
    · exact lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδζ : δ < ζ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  obtain ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1m, h1p, h2m, h2p, N₁, hN₁, hp⟩ :=
    hp γ α₀ hγ hγ2 hα β hβ δ hδ b hb
  refine ⟨a, ha, C₁m, C₁p, C₂m, C₂p, h1m, h1p, h2m, h2p, N₁, hN₁, ?_⟩
  intro N₀ hN₀
  obtain ⟨m, hm, hfail⟩ := hp N₀ hN₀
  refine ⟨m, hm, ?_⟩
  intro Ω _ P hC hcirc μ hGFF hμ hAff hCC hcenter htrivial
  exact ae_eventually_goodScaleCount_of_centered_circle_versions hfull hγ hγ2 hα
    hGFF hμ hAff hCC β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ δ ha.1 hpolar hcenter htrivial
    hδ.1.le hδζ (hfail Ω P hC hcirc μ hGFF hμ hAff hCC 0)

end HarmonicBalls
