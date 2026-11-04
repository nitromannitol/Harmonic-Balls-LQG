import HarmonicBalls.Proofs.Sec8.ObstacleApproximation

/-! # Countable compact obstacles

Finite unions of closed balls with centers in a countable dense set and
rational radii form a countable family of compact neighborhoods.
-/

open Set Metric MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HarmonicBalls

/-- A finite union of closed balls with centers in `D` and rational radii. -/
def rationalBallObstacle (D : Set ℂ) (s : Finset (D × ℚ)) : Set ℂ :=
  ⋃ i ∈ s, closedBall (i.1 : ℂ) (i.2 : ℝ)

/-- Every rational ball obstacle is compact. -/
theorem isCompact_rationalBallObstacle (D : Set ℂ) (s : Finset (D × ℚ)) :
    IsCompact (rationalBallObstacle D s) := by
  apply s.isCompact_biUnion
  intro i hi
  exact isCompact_closedBall _ _

/-- A rational closed ball centered in a dense set can be placed around any
point of an open set, with the entire closed ball still in that set. -/
theorem exists_rational_closedBall_between {D V : Set ℂ} (hD : Dense D)
    (hV : IsOpen V) {x : ℂ} (hx : x ∈ V) :
    ∃ i : D × ℚ, x ∈ ball (i.1 : ℂ) (i.2 : ℝ) ∧
      closedBall (i.1 : ℂ) (i.2 : ℝ) ⊆ V := by
  obtain ⟨ε, hε, hεV⟩ := Metric.isOpen_iff.mp hV x hx
  obtain ⟨d, hd, hdD⟩ := Metric.dense_iff.mp hD x (ε / 8) (by positivity)
  have hdx : dist d x < ε / 8 := by simpa only [mem_ball] using hd
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn (show ε / 4 < ε / 2 by linarith)
  refine ⟨(⟨d, hdD⟩, q), ?_, ?_⟩
  · change dist x d < (q : ℝ)
    rw [dist_comm]
    linarith
  · intro y hy
    apply hεV
    rw [mem_ball]
    change dist y d ≤ (q : ℝ) at hy
    have htriangle := dist_triangle y d x
    linarith

/-- Finite unions of rational closed balls form an outer approximation family
for every compact set and every open neighborhood of it. -/
theorem exists_rationalBallObstacle_between {D K V : Set ℂ} (hD : Dense D)
    (hK : IsCompact K) (hV : IsOpen V) (hKV : K ⊆ V) :
    ∃ s : Finset (D × ℚ), K ⊆ rationalBallObstacle D s ∧
      rationalBallObstacle D s ⊆ V := by
  classical
  have hex : ∀ x : K, ∃ i : D × ℚ, (x : ℂ) ∈ ball (i.1 : ℂ) (i.2 : ℝ) ∧
      closedBall (i.1 : ℂ) (i.2 : ℝ) ⊆ V := fun x =>
    exists_rational_closedBall_between hD hV (hKV x.2)
  choose f hf hsub using hex
  have hcover : K ⊆ ⋃ x : K, ball ((f x).1 : ℂ) ((f x).2 : ℝ) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, hf ⟨x, hx⟩⟩
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun x : K => ball ((f x).1 : ℂ) ((f x).2 : ℝ)) (fun _ => isOpen_ball) hcover
  refine ⟨s.image f, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
    exact mem_iUnion₂.mpr ⟨f y, Finset.mem_image.mpr ⟨y, hy, rfl⟩,
      ball_subset_closedBall hxy⟩
  · intro x hx
    obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hi
    exact hsub y hxi

open MarkovProcess in
/-- For obstacles converging to a compact set through its open neighborhoods,
a strict Brownian avoidance threshold holds for one approximating obstacle. -/
theorem exists_obstacle_of_neighborhood_approximation {U K : Set ℂ}
    (hU : IsOpen U) (hbounded : Bornology.IsBounded U) (hK : IsCompact K)
    (hKU : K ⊆ U) (F : ℕ → Set ℂ) (hKF : ∀ n, K ⊆ F n)
    (happrox : ∀ V : Set ℂ, IsOpen V → K ⊆ V →
      ∃ N, ∀ n ≥ N, F n ⊆ V)
    {u : ℂ} (hu : u ∈ U) (b : ℝ≥0∞)
    (hp : b < planarBrownianMotion u
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Kᶜ p}) :
    ∃ n, F n ⊆ U ∧ b < planarBrownianMotion u
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (F n)ᶜ p} := by
  let Ks : ℕ → Set ℂ := fun n => closure (⋃ j ≥ n, F j)
  have hclosed : ∀ n, IsClosed (Ks n) := fun _ => isClosed_closure
  have hanti : Antitone Ks := by
    intro m n hmn
    apply closure_mono
    refine iUnion₂_subset fun j hj => ?_
    exact subset_iUnion_of_subset j (subset_iUnion_of_subset (hmn.trans hj) (Subset.refl _))
  have hinter : ⋂ n, Ks n = K := by
    apply Subset.antisymm
    · intro x hx
      by_contra hxK
      obtain ⟨V, W, hV, hW, hKV, hxW, hVW⟩ := hK.separation_of_notMem hxK
      obtain ⟨N, hN⟩ := happrox V hV hKV
      have hsub : Ks N ⊆ Wᶜ := by
        apply closure_minimal _ hW.isClosed_compl
        refine iUnion₂_subset fun j hj => ?_
        exact (hN j hj).trans (Set.disjoint_left.mp hVW)
      exact (hsub (mem_iInter.mp hx N)) hxW
    · intro x hx
      apply mem_iInter.mpr
      intro n
      apply subset_closure
      exact mem_iUnion₂.mpr ⟨n, le_rfl, hKF n hx⟩
  obtain ⟨N, hN⟩ := happrox U hU hKU
  obtain ⟨n, hn⟩ := exists_closed_obstacle_approximation_of_avoid_gt
    hU hbounded hKU Ks hclosed hanti hinter hu b hp
  let m := max n N
  have hm : b < planarBrownianMotion u
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Ks m)ᶜ p} := by
    apply hn.trans_le
    apply measure_mono
    intro p hp'
    change ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Ks n)ᶜ p at hp'
    change ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Ks m)ᶜ p
    exact hp'.trans (ContinuousPath.exitTime_mono
      (compl_subset_compl.mpr (hanti (le_max_left n N))) p)
  refine ⟨m, hN m (le_max_right n N), hm.trans_le ?_⟩
  apply measure_mono
  intro p hp'
  change ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (Ks m)ᶜ p at hp'
  change ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime (F m)ᶜ p
  apply hp'.trans
  apply ContinuousPath.exitTime_mono
  apply compl_subset_compl.mpr
  intro x hx
  apply subset_closure
  exact mem_iUnion₂.mpr ⟨m, le_rfl, hx⟩

open MarkovProcess in
/-- A compact obstacle with strict Brownian avoidance probability can be
replaced by one of the countable rational ball obstacles, preserving that
strict probability and enlarging the obstacle. -/
theorem exists_rationalBallObstacle_of_avoid_gt {D U K : Set ℂ} (hD : Dense D)
    (hU : IsOpen U) (hbounded : Bornology.IsBounded U) (hK : IsCompact K)
    (hKU : K ⊆ U) {u : ℂ} (hu : u ∈ U) (b : ℝ≥0∞)
    (hp : b < planarBrownianMotion u
      {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Kᶜ p}) :
    ∃ s : Finset (D × ℚ), K ⊆ rationalBallObstacle D s ∧
      rationalBallObstacle D s ⊆ U ∧ b < planarBrownianMotion u
        {p | ContinuousPath.exitTime U p ≤
          ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ p} := by
  have hex (n : ℕ) : ∃ s : Finset (D × ℚ), K ⊆ rationalBallObstacle D s ∧
      rationalBallObstacle D s ⊆ thickening (1 / ((n : ℝ) + 1)) K :=
    exists_rationalBallObstacle_between hD hK isOpen_thickening
      (self_subset_thickening (by positivity) K)
  choose s hs hsub using hex
  have happrox : ∀ V : Set ℂ, IsOpen V → K ⊆ V →
      ∃ N, ∀ n ≥ N, rationalBallObstacle D (s n) ⊆ V := by
    intro V hV hKV
    obtain ⟨ε, hε, hεV⟩ := hK.exists_thickening_subset_open hV hKV
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
    refine ⟨N, fun n hn => (hsub n).trans ?_⟩
    apply (thickening_mono _ K).trans hεV
    have hden : (N : ℝ) + 1 ≤ (n : ℝ) + 1 := by exact_mod_cast (Nat.add_le_add_right hn 1)
    have hfrac : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) := by
      gcongr
    exact hfrac.trans hN.le
  obtain ⟨n, hnU, hn⟩ := exists_obstacle_of_neighborhood_approximation
    hU hbounded hK hKU (fun n => rationalBallObstacle D (s n)) hs happrox hu b hp
  exact ⟨s n, hs n, hnU, hn⟩

open MarkovProcess in
/-- Under the interior small-ball hitting estimate, a finite atomless measure
passes the good-annulus test exactly when it passes all rational obstacle
tests. The family is countable whenever `D` is countable. -/
theorem isGoodAnnulus_iff_rationalBallObstacles
    {D : Set ℂ} (hD : Dense D) (μ : Measure ℂ) [NullSingletonClass μ]
    (r : ℝ) (hr : 0 < r) (z : ℂ) (a b : ℝ)
    (hfinite : μ (annulus z (3 * r) (5 * r)) ≠ ∞)
    (hthreshold : 0 < ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)))
    (hsmall : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε) :
    IsGoodAnnulus μ r z a b ↔
      ∀ s : Finset (D × ℚ), rationalBallObstacle D s ⊆ annulus z (3 * r) (5 * r) →
        μ (annulus z (3 * r) (5 * r) \ rationalBallObstacle D s) <
          ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) →
        ∀ u ∈ sphere z (4 * r), planarBrownianMotion u
          {p | ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
            ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ p} ≤ ENNReal.ofReal b := by
  let U := annulus z (3 * r) (5 * r)
  have hU : IsOpen U := isOpen_ball.sdiff isClosed_closedBall
  have hbounded : Bornology.IsBounded U := isBounded_ball.subset sdiff_subset
  have hcenter : ∀ u ∈ sphere z (4 * r), u ∈ U := by
    intro u hu
    simp only [mem_sphere] at hu
    change u ∈ ball z (5 * r) \ closedBall z (3 * r)
    simp only [mem_sdiff, mem_ball, mem_closedBall, not_le]
    constructor <;> linarith
  constructor
  · intro hgood s hs hmass u hu
    have h := hgood (U \ rationalBallObstacle D s)
      (hU.measurableSet.diff (isCompact_rationalBallObstacle D s).measurableSet)
      sdiff_subset hmass.le u hu
    have heq : {p : ContinuousPath ℂ | ContinuousPath.exitTime U p ≤
        ContinuousPath.exitTime (U \ rationalBallObstacle D s) p} =
        {p | ContinuousPath.exitTime U p ≤
          ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ p} := by
      ext p
      exact stay_sdiff_iff_avoid U (rationalBallObstacle D s) p
    rw [← heq]
    exact h
  · intro htest
    apply (isGoodAnnulus_iff_compact_obstacles_of_small_ball_hitting
      μ r z a b hfinite hthreshold hsmall).2
    intro K hK hKU hmass u hu
    by_contra hnot
    have hp : ENNReal.ofReal b < planarBrownianMotion u
        {p | ContinuousPath.exitTime U p ≤ ContinuousPath.exitTime Kᶜ p} := by
      have := lt_of_not_ge hnot
      convert this using 1
      congr 1
      ext p
      exact (stay_sdiff_iff_avoid U K p).symm
    obtain ⟨s, hKs, hsU, hprob⟩ := exists_rationalBallObstacle_of_avoid_gt
      hD hU hbounded hK hKU (hcenter u hu) (ENNReal.ofReal b) hp
    have hmass' : μ (U \ rationalBallObstacle D s) < ENNReal.ofReal a * μ U :=
      (measure_mono (show U \ rationalBallObstacle D s ⊆ U \ K from
        fun x hx => ⟨hx.1, fun hxK => hx.2 (hKs hxK)⟩)).trans_lt hmass
    exact (not_le_of_gt hprob) (htest s hsU hmass' u hu)

open MarkovProcess in
/-- A single Borel set of measures represents the good-annulus event on
finite atomless measures with positive mass threshold, conditional on the
interior small-ball hitting estimate. -/
theorem exists_measurable_isGoodAnnulus_on_atomless
    (r : ℝ) (hr : 0 < r) (z : ℂ) (a b : ℝ)
    (hsmall : ∀ u ∈ sphere z (4 * r), ∀ x ∈ annulus z (3 * r) (5 * r), x ≠ u →
      ∀ ε : ℝ≥0∞, 0 < ε → ∃ ρ : ℝ, 0 < ρ ∧
      planarBrownianMotion u
        {p | ¬ ContinuousPath.exitTime (annulus z (3 * r) (5 * r)) p ≤
          ContinuousPath.exitTime (ball x ρ)ᶜ p} < ε) :
    ∃ G : Set (Measure ℂ), MeasurableSet G ∧
      ∀ (μ : Measure ℂ) (_ : NullSingletonClass μ),
        μ (annulus z (3 * r) (5 * r)) ≠ ∞ →
        0 < ENNReal.ofReal a * μ (annulus z (3 * r) (5 * r)) →
        (μ ∈ G ↔ IsGoodAnnulus μ r z a b) := by
  classical
  obtain ⟨D, hDc, hD⟩ := TopologicalSpace.exists_countable_dense ℂ
  let : Countable D := hDc.to_subtype
  let U := annulus z (3 * r) (5 * r)
  let Bad (s : Finset (D × ℚ)) : Set (Measure ℂ) :=
    {μ | rationalBallObstacle D s ⊆ U ∧
      μ (U \ rationalBallObstacle D s) < ENNReal.ofReal a * μ U ∧
      ∃ u ∈ sphere z (4 * r), ENNReal.ofReal b < planarBrownianMotion u
        {p | ContinuousPath.exitTime U p ≤
          ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ p}}
  have hBad (s : Finset (D × ℚ)) : MeasurableSet (Bad s) := by
    have hmass : MeasurableSet {μ : Measure ℂ |
        μ (U \ rationalBallObstacle D s) < ENNReal.ofReal a * μ U} :=
      measurableSet_lt (Measure.measurable_coe
        ((isOpen_ball.sdiff isClosed_closedBall).measurableSet.diff
          (isCompact_rationalBallObstacle D s).measurableSet))
        (measurable_const.mul (Measure.measurable_coe
          (isOpen_ball.sdiff isClosed_closedBall).measurableSet))
    by_cases hcond : rationalBallObstacle D s ⊆ U ∧
        ∃ u ∈ sphere z (4 * r), ENNReal.ofReal b < planarBrownianMotion u
          {p | ContinuousPath.exitTime U p ≤
            ContinuousPath.exitTime (rationalBallObstacle D s)ᶜ p}
    · have heq : Bad s = {μ : Measure ℂ |
          μ (U \ rationalBallObstacle D s) < ENNReal.ofReal a * μ U} := by
        ext μ
        simp only [Bad, mem_ofPred_eq]
        exact ⟨fun h => h.2.1, fun h => ⟨hcond.1, h, hcond.2⟩⟩
      rw [heq]
      exact hmass
    · have heq : Bad s = ∅ := by
        ext μ
        simp only [Bad, mem_ofPred_eq, mem_empty_iff_false, iff_false]
        rintro ⟨hs, _, hp⟩
        exact hcond ⟨hs, hp⟩
      rw [heq]
      exact MeasurableSet.empty
  refine ⟨(⋃ s, Bad s)ᶜ, (MeasurableSet.iUnion hBad).compl, ?_⟩
  intro μ hμ hfinite hthreshold
  let : NullSingletonClass μ := hμ
  rw [isGoodAnnulus_iff_rationalBallObstacles hD μ r hr z a b hfinite hthreshold hsmall]
  simp only [mem_compl_iff, mem_iUnion, Bad, mem_ofPred_eq, not_exists, not_and]
  constructor
  · intro h s hs hm u hu
    exact le_of_not_gt (h s hs hm u hu)
  · intro h s hs hm u hu
    exact not_lt_of_ge (h s hs hm u hu)

end HarmonicBalls
