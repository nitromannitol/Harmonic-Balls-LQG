import HarmonicBalls.Proofs.Sec3.ClusterCompatibility
import Mathlib.Topology.ContinuousMap.Compact
import HarmonicBalls.Proofs.Sec6.PotentialMeasureMeasurable
import HarmonicBalls.Proofs.Sec5.ExitHorizon

/-! # Stability of the shifted obstacle problem in the Green potential -/

namespace HarmonicBalls

open MeasureTheory Metric Set TopologicalSpace

/-- A uniform upper bound on the change of Green potential gives the same
upper bound on the change of the least superharmonic majorant, off the pole. -/
theorem shiftedLeastSupersolution_le_of_greenPotentialBall_le_add
    {μ ν : Measure ℂ} {R t c : ℝ} {z x : ℂ}
    (hne : (shiftedSupersolutions μ R z t).Nonempty)
    (hpot : ∀ y ∈ closedBall (0 : ℂ) R,
      greenPotentialBall ν R y ≤ greenPotentialBall μ R y + c)
    (hx : x ∈ closedBall (0 : ℂ) R) (hxz : x ≠ z) :
    shiftedLeastSupersolution ν R z t x ≤ shiftedLeastSupersolution μ R z t x + c := by
  have hcomp : ∀ w ∈ shiftedSupersolutions μ R z t,
      (fun y => w y + c) ∈ shiftedSupersolutions ν R z t := by
    intro w hw
    refine ⟨hw.1.add continuousOn_const, ?_, ?_⟩
    · have hzero : HasLaplacian (fun _ : ℂ => (1 : ℝ)) 0 0 (ball 0 R) :=
        hasLaplacian_zero_of_harmonicOnNhd isOpen_ball (InnerProductSpace.harmonicOnNhd_const 1)
      simpa using hw.2.1.add_const_mul_of_hasLaplacian_zero hzero c
    · intro y hy hyz
      have hw' := hw.2.2 y hy hyz
      have hp := hpot y hy
      simp only [obstacle] at hw' ⊢
      linarith
  have hbound : shiftedLeastSupersolution ν R z t x - c ≤
      shiftedLeastSupersolution μ R z t x := by
    apply le_csInf (hne.image _)
    rintro _ ⟨w, hw, rfl⟩
    have := shiftedLeastSupersolution_le (hcomp w hw) hx hxz
    linarith
  linarith

/-- The least superharmonic majorant is 1-Lipschitz in the uniform distance
between Green potentials, provided both supersolution classes are nonempty. -/
theorem abs_shiftedLeastSupersolution_sub_le_of_greenPotentialBall
    {μ ν : Measure ℂ} {R t c : ℝ} {z x : ℂ}
    (hμ : (shiftedSupersolutions μ R z t).Nonempty)
    (hν : (shiftedSupersolutions ν R z t).Nonempty)
    (hpot : ∀ y ∈ closedBall (0 : ℂ) R,
      |greenPotentialBall μ R y - greenPotentialBall ν R y| ≤ c)
    (hx : x ∈ closedBall (0 : ℂ) R) (hxz : x ≠ z) :
    |shiftedLeastSupersolution μ R z t x - shiftedLeastSupersolution ν R z t x| ≤ c := by
  have h₁ := shiftedLeastSupersolution_le_of_greenPotentialBall_le_add (μ := ν) (ν := μ) hν
    (fun y hy => by have h := (abs_le.mp (hpot y hy)).2; linarith) hx hxz
  have h₂ := shiftedLeastSupersolution_le_of_greenPotentialBall_le_add (μ := μ) (ν := ν) hμ
    (fun y hy => by have h := (abs_le.mp (hpot y hy)).1; linarith) hx hxz
  apply abs_le.mpr
  constructor <;> linarith

/-- The shifted odometer is 2-Lipschitz in the uniform distance between
Green potentials, at points of the closed ball away from the pole. -/
theorem abs_shiftedOdometer_sub_le_of_greenPotentialBall
    {μ ν : Measure ℂ} {R t c : ℝ} {z x : ℂ}
    (hμ : (shiftedSupersolutions μ R z t).Nonempty)
    (hν : (shiftedSupersolutions ν R z t).Nonempty)
    (hpot : ∀ y ∈ closedBall (0 : ℂ) R,
      |greenPotentialBall μ R y - greenPotentialBall ν R y| ≤ c)
    (hx : x ∈ closedBall (0 : ℂ) R) (hxz : x ≠ z) :
    |shiftedOdometer μ R z t x - shiftedOdometer ν R z t x| ≤ 2 * c := by
  have hmajor := abs_le.mp (abs_shiftedLeastSupersolution_sub_le_of_greenPotentialBall
    hμ hν hpot hx hxz)
  have hpoint := abs_le.mp (hpot x hx)
  apply abs_le.mpr
  simp only [shiftedOdometer, obstacle]
  constructor <;> linarith [hmajor.1, hmajor.2, hpoint.1, hpoint.2]

/-- A real-valued function controlled by the distance between its parameters
factors through a Lipschitz function on the entire parameter space. -/
theorem exists_lipschitz_factor_of_dist_le {A B : Type*} [PseudoMetricSpace B]
    (q : A → B) (f : A → ℝ) (K : NNReal)
    (h : ∀ a b, dist (f a) (f b) ≤ K * dist (q a) (q b)) :
    ∃ g : B → ℝ, LipschitzWith K g ∧ ∀ a, f a = g (q a) := by
  classical
  let v : B → ℝ := fun y => if hy : y ∈ range q then f (Classical.choose hy) else 0
  have hv : ∀ a, v (q a) = f a := by
    intro a
    have ha : q a ∈ range q := ⟨a, rfl⟩
    have hq : q (Classical.choose ha) = q a := Classical.choose_spec ha
    have hd := h (Classical.choose ha) a
    rw [hq, dist_self, mul_zero] at hd
    have he : f (Classical.choose ha) = f a := dist_eq_zero.mp (le_antisymm hd dist_nonneg)
    simpa only [v, dite_eq_left ha] using he
  have hlip : LipschitzOnWith K v (range q) := by
    apply LipschitzOnWith.of_dist_le_mul
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simpa only [hv] using h a b
  obtain ⟨g, hg, heq⟩ := hlip.extend_real
  exact ⟨g, hg, fun a => (hv a).symm.trans (heq ⟨a, rfl⟩)⟩

/-- A measurable continuous-function-valued Green potential yields measurable
fixed-point odometer evaluations whenever the shifted classes are nonempty. -/
theorem measurable_shiftedOdometer_of_measurable_greenPotentialBall
    {Ω : Type*} [MeasurableSpace Ω] (μ : Ω → Measure ℂ)
    {R t : ℝ} {z x : ℂ} (hx : x ∈ closedBall (0 : ℂ) R) (hxz : x ≠ z)
    (hclass : ∀ ω, (shiftedSupersolutions (μ ω) R z t).Nonempty)
    (q : Ω → C(closedBall (0 : ℂ) R, ℝ))
    (hq : ∀ ω y, q ω y = greenPotentialBall (μ ω) R y)
    (hqmeas : Measurable q) :
    Measurable (fun ω => shiftedOdometer (μ ω) R z t x) := by
  have hdist : ∀ a b, dist (shiftedOdometer (μ a) R z t x)
      (shiftedOdometer (μ b) R z t x) ≤ (2 : NNReal) * dist (q a) (q b) := by
    intro a b
    rw [Real.dist_eq]
    apply abs_shiftedOdometer_sub_le_of_greenPotentialBall (hclass a) (hclass b) ?_ hx hxz
    intro y hy
    have hd := ContinuousMap.dist_apply_le_dist (f := q a) (g := q b) ⟨y, hy⟩
    simpa only [Real.dist_eq, hq] using hd
  obtain ⟨g, hg, heq⟩ := exists_lipschitz_factor_of_dist_le q
    (fun ω => shiftedOdometer (μ ω) R z t x) 2 hdist
  have he : (fun ω => shiftedOdometer (μ ω) R z t x) = g ∘ q := by
    funext ω
    exact heq ω
  rw [he]
  exact hg.continuous.measurable.comp hqmeas

/-- Under the same potential measurability hypothesis, a fixed spatial point
belongs to the shifted non-coincidence set on a measurable event. -/
theorem measurableSet_mem_nonCoincidenceSet_of_measurable_greenPotentialBall
    {Ω : Type*} [MeasurableSpace Ω] (μ : Ω → Measure ℂ)
    {R t : ℝ} {z x : ℂ}
    (hclass : ∀ ω, (shiftedSupersolutions (μ ω) R z t).Nonempty)
    (q : Ω → C(closedBall (0 : ℂ) R, ℝ))
    (hq : ∀ ω y, q ω y = greenPotentialBall (μ ω) R y)
    (hqmeas : Measurable q) :
    MeasurableSet {ω | x ∈ nonCoincidenceSet (μ ω) R z t} := by
  by_cases hball : x ∈ ball (0 : ℂ) R
  · by_cases hxz : x = z
    · subst x
      simpa only [mem_nonCoincidenceSet_iff, hball, true_or, and_true, Set.ofPred_true] using
        (MeasurableSet.univ : MeasurableSet (univ : Set Ω))
    · have hm := measurable_shiftedOdometer_of_measurable_greenPotentialBall μ
        (ball_subset_closedBall hball) hxz hclass q hq hqmeas
      simpa only [mem_nonCoincidenceSet_iff, hball, hxz, false_or, true_and] using
        measurableSet_lt measurable_const hm
  · simpa only [mem_nonCoincidenceSet_iff, hball, false_and, Set.ofPred_false] using
      (MeasurableSet.empty : MeasurableSet (∅ : Set Ω))

/-- Pointwise measurability of continuous Green potentials is enough for the
fixed-point event of the shifted non-coincidence set. -/
theorem measurableSet_mem_nonCoincidenceSet_of_greenPotentialBall_sections
    {Ω : Type*} [MeasurableSpace Ω] (μ : Ω → Measure ℂ)
    {R t : ℝ} {z x : ℂ}
    (hclass : ∀ ω, (shiftedSupersolutions (μ ω) R z t).Nonempty)
    (hcont : ∀ ω, ContinuousOn (greenPotentialBall (μ ω) R) (closedBall 0 R))
    (hpoint : ∀ y, Measurable (fun ω => greenPotentialBall (μ ω) R y)) :
    MeasurableSet {ω | x ∈ nonCoincidenceSet (μ ω) R z t} := by
  let q : Ω → C(closedBall (0 : ℂ) R, ℝ) := fun ω =>
    ⟨fun y => greenPotentialBall (μ ω) R y, (hcont ω).domRestrict⟩
  have hq : Measurable q := ContinuousMap.measurable_iff_eval.mpr (fun y => hpoint y)
  exact measurableSet_mem_nonCoincidenceSet_of_measurable_greenPotentialBall μ
    hclass q (fun _ _ => rfl) hq

/-- For discs the two conventions for the Green potential agree. -/
theorem greenPotentialBall_eq_greenPotential (μ : Measure ℂ) (R : ℝ) (x : ℂ) :
    greenPotentialBall μ R x = greenPotential (ball 0 R) μ x := by
  unfold greenPotentialBall greenPotential
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun y => greenFunction_ball_comm R y x)
  · intro y hy
    exact greenFunction_of_notMem_left hy x

/-- The Green potential of a disc at a fixed point is measurable in the measure. -/
theorem measurable_greenPotentialBall_measure (R : ℝ) (x : ℂ) :
    Measurable (fun μ : Measure ℂ => greenPotentialBall μ R x) := by
  simp_rw [greenPotentialBall_eq_greenPotential]
  exact Section6.measurable_greenPotential_measure isOpen_ball isBounded_ball x

/-- A measurable family of locally finite measures satisfying volume growth
has measurable fixed-point cluster membership at positive time. -/
theorem measurableSet_mem_cluster_of_volumeGrowth
    {Ω : Type*} [MeasurableSpace Ω] (μ : Ω → Measure ℂ) (hμ : Measurable μ)
    {R t : ℝ} {z x : ℂ} (hR : 0 < R)
    (hloc : ∀ ω, IsLocallyFiniteMeasure (μ ω))
    (hvol : ∀ ω, ∃ βminus βplus, VolumeGrowth (μ ω) R βminus βplus)
    (hz : z ∈ ball (0 : ℂ) R) (ht : 0 < t) :
    MeasurableSet {ω | x ∈ cluster (μ ω) R z t} := by
  have hcont : ∀ ω, ContinuousOn (greenPotentialBall (μ ω) R) (closedBall 0 R) :=
    fun ω => by
      obtain ⟨βminus, βplus, hv⟩ := hvol ω
      exact greenPotentialBallContinuousStep_holds (μ ω) (hloc ω) R βminus βplus hR hv
  have hclass : ∀ ω, (shiftedSupersolutions (μ ω) R z t).Nonempty := by
    intro ω
    refine ⟨greenPotentialBall (μ ω) R, greenPotentialBall_mem_shiftedSupersolutions ht.le
      (hcont ω) ?_⟩
    obtain ⟨βminus, βplus, hv⟩ := hvol ω
    exact (greenPotentialBallLaplacianStep_holds (μ ω) (hloc ω) R βminus βplus hR hv).laplacianLE
  have heq : {ω | x ∈ cluster (μ ω) R z t} =
      {ω | x ∈ nonCoincidenceSet (μ ω) R z t} := by
    ext ω
    change x ∈ cluster (μ ω) R z t ↔ x ∈ nonCoincidenceSet (μ ω) R z t
    obtain ⟨βminus, βplus, hv⟩ := hvol ω
    rw [(obstacleCompatibilityShiftStep_holds (μ ω) (hloc ω) R βminus βplus hR
      hv z hz t ht).2.2.1]
  rw [heq]
  exact measurableSet_mem_nonCoincidenceSet_of_greenPotentialBall_sections μ hclass hcont
    (fun y => (measurable_greenPotentialBall_measure R y).comp hμ)

/-- Almost-sure volume growth and almost-everywhere measurability of the
measure suffice for almost-sure measurability of fixed-point membership. -/
theorem nullMeasurableSet_mem_cluster_of_ae_volumeGrowth
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (μ : Ω → Measure ℂ)
    (hμ : AEMeasurable μ P) {R t : ℝ} {z x : ℂ} (hR : 0 < R)
    (hgood : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βminus βplus, VolumeGrowth (μ ω) R βminus βplus)
    (hz : z ∈ ball (0 : ℂ) R) (ht : 0 < t) :
    NullMeasurableSet {ω | x ∈ cluster (μ ω) R z t} P := by
  classical
  have hae : ∀ᵐ ω ∂P, (IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βminus βplus, VolumeGrowth (μ ω) R βminus βplus) ∧ μ ω = hμ.mk μ ω :=
    hgood.and hμ.ae_eq_mk
  obtain ⟨N, hNsub, hNmeas, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hae)
  let μ' : Ω → Measure ℂ := fun ω => if ω ∈ N then volume else hμ.mk μ ω
  have hμ'meas : Measurable μ' := measurable_const.ite hNmeas hμ.measurable_mk
  have hloc : ∀ ω, IsLocallyFiniteMeasure (μ' ω) := by
    intro ω
    by_cases hω : ω ∈ N
    · simpa [μ', hω] using (inferInstance : IsLocallyFiniteMeasure (volume : Measure ℂ))
    · have hg : (IsLocallyFiniteMeasure (μ ω) ∧
          ∃ βminus βplus, VolumeGrowth (μ ω) R βminus βplus) ∧ μ ω = hμ.mk μ ω := by
        by_contra hb
        exact hω (hNsub hb)
      simpa only [μ', hω, ↓reduceIte, ← hg.2] using hg.1.1
  have hvol : ∀ ω, ∃ βminus βplus, VolumeGrowth (μ' ω) R βminus βplus := by
    intro ω
    by_cases hω : ω ∈ N
    · exact ⟨2, 1, by simpa [μ', hω] using volumeGrowth_volume R⟩
    · have hg : (IsLocallyFiniteMeasure (μ ω) ∧
          ∃ βminus βplus, VolumeGrowth (μ ω) R βminus βplus) ∧ μ ω = hμ.mk μ ω := by
        by_contra hb
        exact hω (hNsub hb)
      simpa only [μ', hω, ↓reduceIte, ← hg.2] using hg.1.2
  have hset := measurableSet_mem_cluster_of_volumeGrowth (x := x) μ' hμ'meas hR hloc hvol hz ht
  apply hset.nullMeasurableSet.congr
  have hn : ∀ᵐ ω ∂P, ω ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hNzero
  filter_upwards [hn] with ω hω
  have hg : μ ω = hμ.mk μ ω := by
    have hh : (IsLocallyFiniteMeasure (μ ω) ∧
        ∃ βminus βplus, VolumeGrowth (μ ω) R βminus βplus) ∧ μ ω = hμ.mk μ ω := by
      by_contra hb
      exact hω (hNsub hb)
    exact hh.2
  simp only [μ', hω, ↓reduceIte, ← hg]

/-- The countable containment test is null measurable on the original
probability space under the almost-sure volume growth condition. -/
theorem nullMeasurableSet_denseSequenceBallTest_of_ae_volumeGrowth
    {Ω ι : Type*} [MeasurableSpace Ω] [Countable ι] (P : Measure Ω)
    (μ : Ω → Measure ℂ) (hμ : AEMeasurable μ P) {R : ℝ} (hR : 0 < R)
    (hgood : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) ∧
      ∃ βminus βplus, VolumeGrowth (μ ω) R βminus βplus)
    (e : ι → ball (0 : ℂ) R) (r : ℝ) (n : ℕ) :
    NullMeasurableSet {ω | denseSequenceBallTest r
      (fun i t => cluster (μ ω) R (e i) t) n} P := by
  have heq : {ω | denseSequenceBallTest r (fun i t => cluster (μ ω) R (e i) t) n} =
      ⋂ i, ⋂ m, {ω | denseSeq ℂ m ∈ cluster (μ ω) R (e i) (reciprocalTime n) →
        denseSeq ℂ m ∈ closedBall (0 : ℂ) r} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, denseSequenceBallTest]
  rw [heq]
  apply NullMeasurableSet.iInter
  intro i
  apply NullMeasurableSet.iInter
  intro m
  by_cases hm : denseSeq ℂ m ∈ closedBall (0 : ℂ) r
  · simpa only [hm, implies_true, Set.ofPred_true] using
      (nullMeasurableSet_univ : NullMeasurableSet (univ : Set Ω) P)
  · have hh := nullMeasurableSet_mem_cluster_of_ae_volumeGrowth P μ hμ hR hgood
      (e i).property (reciprocalTime n).property (x := denseSeq ℂ m)
    simp only [hm, imp_false]
    exact hh.compl

end HarmonicBalls
