import HarmonicBalls.Proofs.Sec8.MeasurableStartingAtoms
import HarmonicBalls.Proofs.Sec5.OpenMeasureLaw
import Mathlib.MeasureTheory.Measure.Portmanteau
import Mathlib.MeasureTheory.Measure.GiryMonad
import Mathlib.MeasureTheory.SetAlgebra

/-! # Common continuity sets for random measures

A finite average measure selects deterministic balls whose frontiers are null
for almost every measure in a random family.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A uniformly bounded measurable random measure has a finite average. -/
theorem isFiniteMeasure_bind_of_ae_univ_le_one
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X)
    (hν : AEMeasurable ν P) (hbound : ∀ᵐ ω ∂P, ν ω univ ≤ 1) :
    IsFiniteMeasure (P.bind ν) := by
  constructor
  rw [Measure.bind_apply MeasurableSet.univ hν]
  calc
    ∫⁻ ω, ν ω univ ∂P ≤ ∫⁻ _ω, (1 : ℝ≥0∞) ∂P := lintegral_mono_ae hbound
    _ = 1 := by simp
    _ < ∞ := ENNReal.one_lt_top

/-- A null set of the average is null for almost every member of the family. -/
theorem ae_measure_eq_zero_of_bind_eq_zero
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (ν : Ω → Measure X) (hν : AEMeasurable ν P)
    {A : Set X} (hA : MeasurableSet A) (hzero : P.bind ν A = 0) :
    ∀ᵐ ω ∂P, ν ω A = 0 := by
  rw [Measure.bind_apply hA hν] at hzero
  exact (lintegral_eq_zero_iff' ((Measure.measurable_coe hA).comp_aemeasurable hν)).mp hzero

/-- Each nonempty interval contains a radius whose ball frontier is null for
almost every measure in the family. -/
theorem exists_ae_null_frontier_ball
    {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X)
    (hν : AEMeasurable ν P) (hbound : ∀ᵐ ω ∂P, ν ω univ ≤ 1)
    (x : X) {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Ioo a b, ∀ᵐ ω ∂P, ν ω (frontier (ball x r)) = 0 := by
  let : IsFiniteMeasure (P.bind ν) := isFiniteMeasure_bind_of_ae_univ_le_one P ν hν hbound
  obtain ⟨r, hr, hz⟩ := exists_null_frontier_thickening (P.bind ν) ({x} : Set X) hab
  refine ⟨r, hr, ?_⟩
  apply ae_measure_eq_zero_of_bind_eq_zero P ν hν isClosed_frontier.measurableSet
  simpa only [Metric.thickening_singleton] using hz

/-- Countably many prescribed intervals admit deterministic radii whose ball
frontiers are simultaneously null almost surely. -/
theorem exists_ae_null_frontier_balls
    {Ω X : Type*} [MeasurableSpace Ω] [PseudoMetricSpace X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (P : Measure Ω) [IsProbabilityMeasure P] (ν : Ω → Measure X)
    (hν : AEMeasurable ν P) (hbound : ∀ᵐ ω ∂P, ν ω univ ≤ 1)
    (x : ℕ → X) (a b : ℕ → ℝ) (hab : ∀ n, a n < b n) :
    ∃ r : ℕ → ℝ, (∀ n, r n ∈ Ioo (a n) (b n)) ∧
      ∀ᵐ ω ∂P, ∀ n, ν ω (frontier (ball (x n) (r n))) = 0 := by
  choose r hr hz using fun n => exists_ae_null_frontier_ball P ν hν hbound (x n) (hab n)
  exact ⟨r, hr, ae_all_iff.mpr hz⟩

/-- On a finite-mass localization set, one can choose countably many ball
frontiers that are simultaneously null for the original random measures. -/
theorem exists_ae_null_frontier_balls_of_local_finiteness
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : Set ℂ) (hB : MeasurableSet B) (hfin : ∀ᵐ ω ∂P, μ ω B ≠ ∞)
    (x : ℕ → ℂ) (a b : ℕ → ℝ) (hab : ∀ n, a n < b n)
    (hinside : ∀ n r, r ∈ Ioo (a n) (b n) → frontier (ball (x n) r) ⊆ B) :
    ∃ r : ℕ → ℝ, (∀ n, r n ∈ Ioo (a n) (b n)) ∧
      ∀ᵐ ω ∂P, ∀ n, μ ω (frontier (ball (x n) (r n))) = 0 := by
  let ν : Ω → Measure ℂ := fun ω => normalizedRestriction (μ ω) B
  have hν : AEMeasurable ν P := (measurable_normalizedRestriction_measure B hB).comp_aemeasurable hμ
  have hbound : ∀ᵐ ω ∂P, ν ω univ ≤ 1 := by
    apply Eventually.of_forall
    intro ω
    change (normalizedRestriction (μ ω) B) univ ≤ 1
    simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul, Measure.restrict_apply_univ]
    by_cases hz : μ ω B = 0
    · simp [hz]
    by_cases ht : μ ω B = ∞
    · simp [ht]
    simp [ENNReal.inv_mul_cancel hz ht]
  obtain ⟨r, hr, hz⟩ := exists_ae_null_frontier_balls P ν hν hbound x a b hab
  refine ⟨r, hr, ?_⟩
  filter_upwards [hz, hfin] with ω hzω hfinω
  intro n
  have hzero := hzω n
  change normalizedRestriction (μ ω) B (frontier (ball (x n) (r n))) = 0 at hzero
  simp only [normalizedRestriction, Measure.smul_apply, smul_eq_mul,
    Measure.restrict_apply isClosed_frontier.measurableSet,
    inter_eq_left.mpr (hinside n (r n) (hr n)), mul_eq_zero,
    ENNReal.inv_ne_zero.mpr hfinω, false_or] at hzero
  exact hzero

/-- Intersections of continuity sets are continuity sets. -/
theorem measure_frontier_inter_eq_zero {X : Type*} [TopologicalSpace X]
    [MeasurableSpace X] (μ : Measure X) (A B : Set X)
    (hA : μ (frontier A) = 0) (hB : μ (frontier B) = 0) :
    μ (frontier (A ∩ B)) = 0 := by
  apply measure_mono_null ((frontier_inter_subset A B).trans
    (union_subset_union inter_subset_left inter_subset_right))
  exact measure_union_null hA hB

/-- Finite intersections of common continuity sets are again common
continuity sets. -/
theorem ae_measure_frontier_finset_iInter_eq_zero
    {Ω X : Type*} [MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
    (P : Measure Ω) (μ : Ω → Measure X) (S : ℕ → Set X)
    (hS : ∀ᵐ ω ∂P, ∀ n, μ ω (frontier (S n)) = 0) :
    ∀ᵐ ω ∂P, ∀ F : Finset ℕ, μ ω (frontier (⋂ n ∈ F, S n)) = 0 := by
  filter_upwards [hS] with ω hω
  intro F
  induction F using Finset.induction_on with
  | empty => simp
  | @insert n F hn ih =>
    rw [Finset.set_biInter_insert]
    exact measure_frontier_inter_eq_zero (μ ω) (S n) (⋂ i ∈ F, S i) (hω n) ih

/-- A whole-plane LQG measure admits common continuity balls inside every
bounded localization set. -/
theorem IsWholePlaneGFF.exists_ae_lqg_null_frontier_balls
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (R : ℝ) (x : ℕ → ℂ) (a b : ℕ → ℝ) (hab : ∀ n, a n < b n)
    (hinside : ∀ n r, r ∈ Ioo (a n) (b n) →
      frontier (ball (x n) r) ⊆ ball (0 : ℂ) R) :
    ∃ r : ℕ → ℝ, (∀ n, r n ∈ Ioo (a n) (b n)) ∧
      ∀ᵐ ω ∂P, ∀ n, μ ω (frontier (ball (x n) (r n))) = 0 := by
  apply exists_ae_null_frontier_balls_of_local_finiteness P μ
    (hGFF.aemeasurable_lqgMeasure hμ) (ball 0 R) isOpen_ball.measurableSet
  · filter_upwards [hμ] with ω hω
    let : IsLocallyFiniteMeasure (μ ω) := hω.isLocallyFiniteMeasure
    exact measure_ball_lt_top.ne
  · exact hab
  · exact hinside

/-- A countable family of open continuity sets extends to a countable open
π-system containing the whole space, without changing its generated
sigma-algebra. -/
theorem exists_common_continuity_piSystem
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (S : ℕ → Set ℂ) (hopen : ∀ n, IsOpen (S n))
    (hnull : ∀ᵐ ω ∂P, ∀ n, μ ω (frontier (S n)) = 0) :
    ∃ T : Set (Set ℂ), T.Countable ∧ IsPiSystem T ∧ univ ∈ T ∧
      (∀ A ∈ T, IsOpen A) ∧
      MeasurableSpace.generateFrom T = MeasurableSpace.generateFrom (range S) ∧
      ∀ᵐ ω ∂P, ∀ A ∈ T, μ ω (frontier A) = 0 := by
  let B : Set (Set ℂ) := range S ∪ {univ}
  let T := generatePiSystem B
  have hcount : B.Countable := (countable_range S).union (countable_singleton univ)
  have hTalg : T ⊆ generateSetAlgebra B := by
    apply generatePiSystem_min self_subset_generateSetAlgebra
    intro A hA C hC _
    exact isSetAlgebra_generateSetAlgebra.inter_mem hA hC
  have hBopen : ∀ A ∈ B, IsOpen A := by
    intro A hA
    rcases hA with ⟨n, rfl⟩ | hA
    · exact hopen n
    · simpa only [mem_singleton_iff] using hA ▸ isOpen_univ
  have hTopen : ∀ A ∈ T, IsOpen A := generatePiSystem_min hBopen isPiSystem_isOpen
  refine ⟨T, (countable_generateSetAlgebra hcount).mono hTalg,
    isPiSystem_generatePiSystem B, subset_generatePiSystem_self B (Or.inr rfl),
    hTopen, ?_, ?_⟩
  · apply le_antisymm
    · apply MeasurableSpace.generateFrom_le
      intro A hA
      let : MeasurableSpace ℂ := MeasurableSpace.generateFrom (range S)
      apply generatePiSystem_measurableSet (S := B) _ A hA
      intro V hV
      rcases hV with hV | hV
      · exact MeasurableSpace.measurableSet_generateFrom hV
      · simpa only [mem_singleton_iff] using hV ▸ @MeasurableSet.univ ℂ
          (MeasurableSpace.generateFrom (range S))
    · exact MeasurableSpace.generateFrom_mono (fun A hA =>
        subset_generatePiSystem_self B (Or.inl hA))
  · filter_upwards [hnull] with ω hω
    intro A hA
    induction hA using generatePiSystem_induction with
    | base A hA =>
      rcases hA with ⟨n, rfl⟩ | hA
      · exact hω n
      · simpa only [mem_singleton_iff] using hA ▸ (by simp : μ ω (frontier univ) = 0)
    | inter A C hA hC hne ihA ihC =>
      exact measure_frontier_inter_eq_zero (μ ω) A C ihA ihC

/-- Common continuity of the test sets and the exhaustion sets supplies all
four frontier conditions used in normalized mass convergence. -/
theorem ae_frontiers_intersections_of_common_continuity
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (E : ℕ → Set ℂ) (T : Set (Set ℂ))
    (hE : ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (E n)) = 0) ∧
      μ ω (frontier (⋃ n, E n)) = 0)
    (hT : ∀ᵐ ω ∂P, ∀ A ∈ T, μ ω (frontier A) = 0) :
    ∀ᵐ ω ∂P, ∀ A ∈ T,
      (∀ n, μ ω (frontier (E n)) = 0 ∧ μ ω (frontier (A ∩ E n)) = 0) ∧
      μ ω (frontier (⋃ n, E n)) = 0 ∧ μ ω (frontier (A ∩ ⋃ n, E n)) = 0 := by
  filter_upwards [hE, hT] with ω hEω hTω
  intro A hA
  refine ⟨fun n => ⟨hEω.1 n, ?_⟩, hEω.2, ?_⟩
  · exact measure_frontier_inter_eq_zero (μ ω) A (E n) (hTω A hA) (hEω.1 n)
  · exact measure_frontier_inter_eq_zero (μ ω) A (⋃ n, E n) (hTω A hA) hEω.2

/-- A separate finite-mass localization can be used for each prescribed ball.
This permits the selected family to cover the whole plane. -/
theorem exists_ae_null_frontier_balls_of_localizations
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P)
    (B : ℕ → Set ℂ) (hB : ∀ n, MeasurableSet (B n))
    (hfin : ∀ n, ∀ᵐ ω ∂P, μ ω (B n) ≠ ∞)
    (x : ℕ → ℂ) (a b : ℕ → ℝ) (hab : ∀ n, a n < b n)
    (hinside : ∀ n r, r ∈ Ioo (a n) (b n) → frontier (ball (x n) r) ⊆ B n) :
    ∃ r : ℕ → ℝ, (∀ n, r n ∈ Ioo (a n) (b n)) ∧
      ∀ᵐ ω ∂P, ∀ n, μ ω (frontier (ball (x n) (r n))) = 0 := by
  have hone (n : ℕ) : ∃ r ∈ Ioo (a n) (b n),
      ∀ᵐ ω ∂P, μ ω (frontier (ball (x n) r)) = 0 := by
    obtain ⟨r, hr, hz⟩ := exists_ae_null_frontier_balls_of_local_finiteness P μ hμ
      (B n) (hB n) (hfin n) (fun _ => x n) (fun _ => a n) (fun _ => b n)
      (fun _ => hab n) (fun _ => hinside n)
    exact ⟨r 0, hr 0, hz.mono (fun _ h => h 0)⟩
  choose r hr hz using hone
  exact ⟨r, hr, ae_all_iff.mpr hz⟩

/-- LQG continuity-ball selection with a separate bounding disk for each ball. -/
theorem IsWholePlaneGFF.exists_ae_lqg_null_frontier_balls_local
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (R : ℕ → ℝ) (x : ℕ → ℂ) (a b : ℕ → ℝ) (hab : ∀ n, a n < b n)
    (hinside : ∀ n r, r ∈ Ioo (a n) (b n) →
      frontier (ball (x n) r) ⊆ ball (0 : ℂ) (R n)) :
    ∃ r : ℕ → ℝ, (∀ n, r n ∈ Ioo (a n) (b n)) ∧
      ∀ᵐ ω ∂P, ∀ n, μ ω (frontier (ball (x n) (r n))) = 0 := by
  apply exists_ae_null_frontier_balls_of_localizations P μ
    (hGFF.aemeasurable_lqgMeasure hμ) (fun n => ball 0 (R n))
    (fun _ => isOpen_ball.measurableSet) _ x a b hab hinside
  intro n
  filter_upwards [hμ] with ω hω
  let : IsLocallyFiniteMeasure (μ ω) := hω.isLocallyFiniteMeasure
  exact measure_ball_lt_top.ne

/-- The bounding disks in LQG continuity-ball selection can always be chosen
large enough around the prescribed centers. -/
theorem IsWholePlaneGFF.exists_ae_lqg_null_frontier_balls_unbounded
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (x : ℕ → ℂ) (a b : ℕ → ℝ) (hab : ∀ n, a n < b n) :
    ∃ r : ℕ → ℝ, (∀ n, r n ∈ Ioo (a n) (b n)) ∧
      ∀ᵐ ω ∂P, ∀ n, μ ω (frontier (ball (x n) (r n))) = 0 := by
  apply hGFF.exists_ae_lqg_null_frontier_balls_local P hμ
    (fun n => dist (x n) 0 + max (b n) 0 + 1) x a b hab
  intro n r hr z hz
  have hs := frontier_ball_subset_sphere hz
  rw [mem_sphere] at hs
  rw [mem_ball]
  have ht := dist_triangle z (x n) 0
  have hb := le_max_left (b n) (0 : ℝ)
  linarith [hr.2]

/-- Balls with dense centers and radii comparable to reciprocal integers form
a topological basis. -/
theorem isTopologicalBasis_selected_balls (c : ℕ → ℂ) (hc : DenseRange c)
    (r : ℕ → ℝ)
    (hr : ∀ n, 1 / (2 * ((Nat.unpair n).2 + 1 : ℝ)) < r n ∧
      r n < 1 / ((Nat.unpair n).2 + 1 : ℝ)) :
    TopologicalSpace.IsTopologicalBasis (range fun n => ball (c (Nat.unpair n).1) (r n)) := by
  apply TopologicalSpace.isTopologicalBasis_of_isOpen_of_nhds
  · rintro _ ⟨n, rfl⟩
    exact isOpen_ball
  · intro z U hz hU
    obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU z hz
    obtain ⟨k, hk⟩ := exists_nat_one_div_lt (half_pos hε)
    let d : ℝ := 1 / ((k : ℝ) + 1)
    have hd : 0 < d := by dsimp [d]; positivity
    obtain ⟨j, hj⟩ := hc.exists_dist_lt z (show 0 < d / 4 by positivity)
    let n := Nat.pair j k
    have hnr : d / 2 < r n ∧ r n < d := by
      simpa [n, d, Nat.unpair_pair, div_eq_mul_inv, mul_inv_rev, mul_assoc,
        mul_comm, mul_left_comm] using hr n
    refine ⟨ball (c j) (r n), ⟨n, ?_⟩, ?_, ?_⟩
    · simp [n, Nat.unpair_pair]
    · rw [mem_ball]
      linarith [hnr.1]
    · intro w hw
      apply hεU
      rw [mem_ball] at hw ⊢
      have ht := dist_triangle w (c j) z
      have hj' : dist (c j) z < d / 4 := by simpa [dist_comm] using hj
      change d < ε / 2 at hk
      linarith [hnr.2]

/-- A whole-plane LQG measure has a deterministic countable open generating
π-system whose sets are continuity sets almost surely. -/
theorem IsWholePlaneGFF.exists_ae_lqg_continuity_piSystem
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∃ T : Set (Set ℂ), T.Countable ∧ IsPiSystem T ∧ univ ∈ T ∧
      (∀ A ∈ T, IsOpen A) ∧
      (inferInstance : MeasurableSpace ℂ) = MeasurableSpace.generateFrom T ∧
      ∀ᵐ ω ∂P, ∀ A ∈ T, μ ω (frontier A) = 0 := by
  obtain ⟨c, hc⟩ := TopologicalSpace.exists_dense_seq ℂ
  let x : ℕ → ℂ := fun n => c (Nat.unpair n).1
  let a : ℕ → ℝ := fun n => 1 / (2 * ((Nat.unpair n).2 + 1 : ℝ))
  let b : ℕ → ℝ := fun n => 1 / ((Nat.unpair n).2 + 1 : ℝ)
  have hab (n : ℕ) : a n < b n := by
    dsimp [a, b]
    have hp : (0 : ℝ) < ((Nat.unpair n).2 : ℝ) + 1 := by positivity
    apply div_lt_div_of_pos_left (by norm_num) (by positivity)
    linarith
  obtain ⟨r, hr, hz⟩ := hGFF.exists_ae_lqg_null_frontier_balls_unbounded P hμ x a b hab
  let S : ℕ → Set ℂ := fun n => ball (x n) (r n)
  have hbasis : TopologicalSpace.IsTopologicalBasis (range S) :=
    isTopologicalBasis_selected_balls c hc r hr
  obtain ⟨T, hcount, hpi, huniv, hopen, hgen, hnull⟩ :=
    exists_common_continuity_piSystem P μ S (fun _ => isOpen_ball) hz
  refine ⟨T, hcount, hpi, huniv, hopen, ?_, hnull⟩
  calc
    (inferInstance : MeasurableSpace ℂ) = borel ℂ := BorelSpace.measurable_eq
    _ = MeasurableSpace.generateFrom (range S) := hbasis.borel_eq_generateFrom
    _ = MeasurableSpace.generateFrom T := hgen.symm

end HarmonicBalls
