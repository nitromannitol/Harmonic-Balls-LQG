import HarmonicBalls.Draft.Section5
import HarmonicBalls.Proofs.Sec5.SupersolutionScaling
import HarmonicBalls.Proofs.Sec5.ScaleInvariance
import HarmonicBalls.Draft.Section3

/-! # Measurable cluster operations -/

namespace HarmonicBalls

universe u

open MeasureTheory Metric Set TopologicalSpace ProbabilityTheory Filter
open scoped Pointwise

/-- An open set has the same closure as its intersection with a fixed
countable dense set. -/
theorem closure_eq_closure_inter_denseSeq {U : Set ℂ} (hU : IsOpen U) :
    closure U = closure (U ∩ Set.range (denseSeq ℂ)) := by
  apply Subset.antisymm
  · exact closure_minimal ((denseRange_denseSeq ℂ).open_subset_closure_inter hU) isClosed_closure
  · exact closure_mono inter_subset_left

/-- Membership in the closure of an open set is determined by the values of
its indicator on a countable dense sequence. -/
theorem mem_closure_iff_denseSeq {U : Set ℂ} (hU : IsOpen U) (x : ℂ) :
    x ∈ closure U ↔ ∀ n : ℕ, ∃ m : ℕ,
      denseSeq ℂ m ∈ U ∧ dist x (denseSeq ℂ m) < 1 / ((n : ℝ) + 1) := by
  rw [closure_eq_closure_inter_denseSeq hU, Metric.mem_closure_iff]
  constructor
  · intro h n
    obtain ⟨y, ⟨hy, m, rfl⟩, hd⟩ := h (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨m, hy, hd⟩
  · intro h ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨m, hm, hd⟩ := h n
    exact ⟨denseSeq ℂ m, ⟨hm, ⟨m, rfl⟩⟩, hd.trans hn⟩

/-- Taking the closure of a measurable open-set-valued map is measurable for
the pointwise measurable structure on sets. -/
theorem measurable_closure_of_isOpen {Ω : Type*} [MeasurableSpace Ω]
    {U : Ω → Set ℂ} (hU : Measurable U) (hopen : ∀ ω, IsOpen (U ω)) :
    Measurable (fun ω => closure (U ω)) := by
  apply Measurable.of_eval
  intro x
  have hmeas : Measurable (fun ω => ∀ n : ℕ, ∃ m : ℕ,
      denseSeq ℂ m ∈ U ω ∧ dist x (denseSeq ℂ m) < 1 / ((n : ℝ) + 1)) := by
    apply Measurable.forall
    intro n
    apply Measurable.exists
    intro m
    exact ((measurable_pi_apply (denseSeq ℂ m)).comp hU).and measurable_const
  convert hmeas using 1
  funext ω
  exact propext (mem_closure_iff_denseSeq (hopen ω) x)

/-- Pointwise complementation is measurable on set-valued maps. -/
theorem measurable_set_compl {Ω : Type*} [MeasurableSpace Ω]
    {U : Ω → Set ℂ} (hU : Measurable U) : Measurable (fun ω => (U ω)ᶜ) := by
  apply Measurable.of_eval
  intro x
  exact ((measurable_pi_apply x).comp hU).not

/-- The regularization of a measurable open-set-valued map is measurable. -/
theorem measurable_interior_closure_of_isOpen {Ω : Type*} [MeasurableSpace Ω]
    {U : Ω → Set ℂ} (hU : Measurable U) (hopen : ∀ ω, IsOpen (U ω)) :
    Measurable (fun ω => interior (closure (U ω))) := by
  have hc := measurable_closure_of_isOpen hU hopen
  have hc' := measurable_set_compl hc
  have hcc := measurable_closure_of_isOpen hc' (fun _ => isClosed_closure.isOpen_compl)
  simpa only [interior_eq_compl_closure_compl] using measurable_set_compl hcc

/-- Closure remains almost-everywhere measurable for an almost surely open
set-valued map. -/
theorem aemeasurable_closure_of_ae_isOpen {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : Ω → Set ℂ} (hU : AEMeasurable U P)
    (hopen : ∀ᵐ ω ∂P, IsOpen (U ω)) : AEMeasurable (fun ω => closure (U ω)) P := by
  classical
  let V := hU.mk U
  have hv : ∀ᵐ ω ∂P, IsOpen (V ω) := by
    filter_upwards [hopen, hU.ae_eq_mk] with ω ho he
    change IsOpen (hU.mk U ω)
    rwa [← he]
  obtain ⟨N, hNsub, hNmeas, hNnull⟩ := exists_measurable_superset_of_null (ae_iff.mp hv)
  let W : Ω → Set ℂ := fun ω => if ω ∈ N then ∅ else V ω
  have hW : Measurable W := Measurable.ite hNmeas measurable_const hU.measurable_mk
  have hWopen (ω : Ω) : IsOpen (W ω) := by
    by_cases hω : ω ∈ N
    · simp [W, hω]
    · simpa only [W, hω, ite_false] using (not_not.mp fun hn => hω (hNsub hn))
  have hNae : ∀ᵐ ω ∂P, ω ∉ N := by
    apply ae_iff.mpr
    simpa only [not_not, Set.ofPred_mem_eq] using hNnull
  have heq : ∀ᵐ ω ∂P, closure (W ω) = closure (U ω) := by
    filter_upwards [hU.ae_eq_mk, hNae] with ω hω hωN
    change U ω = V ω at hω
    simp only [W, hωN, ite_false, ← hω]
  exact (measurable_closure_of_isOpen hW hWopen).aemeasurable.congr heq

/-- Regularization preserves almost-everywhere measurability for an almost
surely open set-valued map. -/
theorem aemeasurable_interior_closure_of_ae_isOpen {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {U : Ω → Set ℂ} (hU : AEMeasurable U P)
    (hopen : ∀ᵐ ω ∂P, IsOpen (U ω)) :
    AEMeasurable (fun ω => interior (closure (U ω))) P := by
  have hc := aemeasurable_closure_of_ae_isOpen hU hopen
  have hc' : AEMeasurable (fun ω => (closure (U ω))ᶜ) P :=
    (measurable_set_compl measurable_id).comp_aemeasurable hc
  have hcc := aemeasurable_closure_of_ae_isOpen hc'
    (Filter.Eventually.of_forall fun _ => isClosed_closure.isOpen_compl)
  have hcomp := (measurable_set_compl measurable_id).comp_aemeasurable hcc
  simpa only [Function.comp_def, id_eq, interior_eq_compl_closure_compl] using hcomp

/-- Regularization commutes with dilation of the cluster and its measure. -/
theorem regularizedCluster_comp_real_smul {μ : Measure ℂ} {R k c t : ℝ} {z : ℂ}
    (hk : 0 < k) (hc : 0 < c) (ht : 0 ≤ t) :
    regularizedCluster (ENNReal.ofReal c • Measure.map (fun x : ℂ => k⁻¹ • x) μ) R z (c * t) =
      (fun x : ℂ => k • x) ⁻¹' regularizedCluster μ (k * R) (k • z) t := by
  let e : ℂ ≃ₜ ℂ := Homeomorph.smulOfNeZero k hk.ne'
  unfold regularizedCluster
  rw [cluster_comp_real_smul hk hc ht]
  exact (congrArg interior (e.preimage_closure _).symm).trans (e.preimage_interior _).symm

/-- Measurability of each least-supersolution evaluation gives measurability
of the entire cluster family, simultaneously in the time and spatial
coordinates of the pointwise measurable structure. -/
theorem measurable_cluster_family_of_measurable_leastSupersolution
    {Ω : Type*} [MeasurableSpace Ω] (ν : Ω → Measure ℂ) (R : ℝ) (z : ℂ)
    (hv : ∀ (t : Set.Ioi (0 : ℝ)) (x : ℂ),
      Measurable (fun ω => leastSupersolution (ν ω) R z t x)) :
    Measurable (fun ω (t : Set.Ioi (0 : ℝ)) => cluster (ν ω) R z t) := by
  apply Measurable.of_eval
  intro t
  apply Measurable.of_eval
  intro x
  change Measurable (fun ω => x ∈ cluster (ν ω) R z t)
  simp only [cluster, mem_ofPred_eq]
  exact measurable_const.and (measurable_const.or (measurable_const.lt (hv t x)))

/-- The closure of the part of a set seen by a fixed countable dense
sequence. It agrees with ordinary closure for open sets. -/
def denseSequenceClosure (U : Set ℂ) : Set ℂ := closure (U ∩ Set.range (denseSeq ℂ))

/-- Membership in the countable decoder is determined by countably many
point evaluations. -/
theorem mem_denseSequenceClosure_iff (U : Set ℂ) (x : ℂ) :
    x ∈ denseSequenceClosure U ↔ ∀ n : ℕ, ∃ m : ℕ,
      denseSeq ℂ m ∈ U ∧ dist x (denseSeq ℂ m) < 1 / ((n : ℝ) + 1) := by
  rw [denseSequenceClosure, Metric.mem_closure_iff]
  constructor
  · intro h n
    obtain ⟨y, ⟨hy, m, rfl⟩, hd⟩ := h (1 / ((n : ℝ) + 1)) (by positivity)
    exact ⟨m, hy, hd⟩
  · intro h ε hε
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
    obtain ⟨m, hm, hd⟩ := h n
    exact ⟨denseSeq ℂ m, ⟨hm, ⟨m, rfl⟩⟩, hd.trans hn⟩

/-- The countable closure decoder is measurable on all subsets of the plane. -/
theorem measurable_denseSequenceClosure : Measurable denseSequenceClosure := by
  apply Measurable.of_eval
  intro x
  have hmeas : Measurable (fun U : Set ℂ => ∀ n : ℕ, ∃ m : ℕ,
      denseSeq ℂ m ∈ U ∧ dist x (denseSeq ℂ m) < 1 / ((n : ℝ) + 1)) := by
    apply Measurable.forall
    intro n
    apply Measurable.exists
    intro m
    exact (measurable_pi_apply (denseSeq ℂ m)).and measurable_const
  convert hmeas using 1
  funext U
  exact propext (mem_denseSequenceClosure_iff U x)

/-- A measurable extension of open-set regularization to arbitrary subsets. -/
def denseSequenceRegularization (U : Set ℂ) : Set ℂ :=
  (denseSequenceClosure ((denseSequenceClosure U)ᶜ))ᶜ

/-- The regularization decoder is measurable on all subsets of the plane. -/
theorem measurable_denseSequenceRegularization : Measurable denseSequenceRegularization := by
  unfold denseSequenceRegularization
  exact measurable_set_compl (measurable_denseSequenceClosure.comp
    (measurable_set_compl measurable_denseSequenceClosure))

/-- On open sets the regularization decoder is the interior of the closure. -/
theorem denseSequenceRegularization_eq {U : Set ℂ} (hU : IsOpen U) :
    denseSequenceRegularization U = interior (closure U) := by
  have hc : denseSequenceClosure U = closure U := (closure_eq_closure_inter_denseSeq hU).symm
  have hc' : denseSequenceClosure (closure U)ᶜ = closure (closure U)ᶜ :=
    (closure_eq_closure_inter_denseSeq isClosed_closure.isOpen_compl).symm
  rw [denseSequenceRegularization, hc, hc', interior_eq_compl_closure_compl]

/-- Applying the regularization decoder simultaneously to a set-valued
family is measurable in the pointwise measurable structure. -/
theorem measurable_denseSequenceRegularization_family {ι : Type*} :
    Measurable (fun F : ι → Set ℂ => fun i => denseSequenceRegularization (F i)) := by
  apply Measurable.of_eval
  intro i
  exact measurable_denseSequenceRegularization.comp (measurable_pi_apply i)

/-- Equal laws of almost surely open set-valued families imply equal laws of
their regularizations, simultaneously for every index. -/
theorem identDistrib_regularized_family {Ω Ω' ι : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {Q : Measure Ω'}
    {X : Ω → ι → Set ℂ} {Y : Ω' → ι → Set ℂ} (hd : IdentDistrib X Y P Q)
    (hX : ∀ᵐ ω ∂P, ∀ i, IsOpen (X ω i))
    (hY : ∀ᵐ ω ∂Q, ∀ i, IsOpen (Y ω i)) :
    IdentDistrib (fun ω i => interior (closure (X ω i)))
      (fun ω i => interior (closure (Y ω i))) P Q := by
  have h := hd.comp (measurable_denseSequenceRegularization_family (ι := ι))
  have hx : ∀ᵐ ω ∂P, (fun i => denseSequenceRegularization (X ω i)) =
      (fun i => interior (closure (X ω i))) := by
    filter_upwards [hX] with ω hω
    funext i
    exact denseSequenceRegularization_eq (hω i)
  have hy : ∀ᵐ ω ∂Q, (fun i => denseSequenceRegularization (Y ω i)) =
      (fun i => interior (closure (Y ω i))) := by
    filter_upwards [hY] with ω hω
    funext i
    exact denseSequenceRegularization_eq (hω i)
  exact ((IdentDistrib.of_ae_eq h.aemeasurable_fst hx).symm.trans h).trans
    (IdentDistrib.of_ae_eq h.aemeasurable_snd hy)

/-- The conditional cluster scale-invariance law also holds for the family
of regularized clusters, simultaneously at all positive times. -/
theorem regularizedClusterScaleInvariance_of_measurable
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hmeas : ClusterFamilyMeasurabilityStep.{u}) (hopen : ClusterOpenLaplacianStmt.{u})
    {k : ℝ} (hk : 0 < k) {z : ℂ} (hz : z ∈ ball (0 : ℂ) 1) :
    IdentDistrib (fun ω (t : Ioi (0 : ℝ)) => regularizedCluster (μ ω) 1 z t)
      (fun ω (t : Ioi (0 : ℝ)) => k⁻¹ • regularizedCluster (μ ω) k (k • z)
        (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0)) * t)) P P := by
  have hdist := clusterScaleInvariance_of_measurable h hAff hCC hγ hγ2 hα hμ hmeas hk hz
  have hz' : k • z ∈ ball (0 : ℂ) k := by
    simp only [mem_ball_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hk] at hz ⊢
    nlinarith
  have hX : ∀ᵐ ω ∂P, ∀ t : Ioi (0 : ℝ), IsOpen (cluster (μ ω) 1 z t) := by
    filter_upwards [hopen γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ] with ω hω t
    exact (hω t 1 t.property zero_lt_one z hz).1
  have hY : ∀ᵐ ω ∂P, ∀ t : Ioi (0 : ℝ),
      IsOpen (k⁻¹ • cluster (μ ω) k (k • z)
        (Real.exp (γ * (lqgQ γ * Real.log k + fieldCircleAverage α₀ (hcirc ω) k 0)) * t)) := by
    filter_upwards [hopen γ α₀ hγ hγ2 hα Ω P hC hcirc μ h hμ] with ω hω t
    have ht : 0 < Real.exp (γ * (lqgQ γ * Real.log k +
        fieldCircleAverage α₀ (hcirc ω) k 0)) * (t : ℝ) :=
      mul_pos (Real.exp_pos _) t.property
    exact (hω _ k ht hk _ hz').1.smul₀ (inv_ne_zero hk.ne')
  have hreg := identDistrib_regularized_family hdist hX hY
  simpa only [regularizedCluster, closure_smul₀' (inv_ne_zero hk.ne'),
    interior_smul₀ (inv_ne_zero hk.ne')] using hreg

/-- Borel measurability of least-supersolution evaluations is sufficient for
the cluster-family measurability step of Lemma 5.7. -/
theorem clusterFamilyMeasurabilityStep_of_leastSupersolution
    (hv : ∀ z ∈ ball (0 : ℂ) 1, ∀ (t : Ioi (0 : ℝ)) (x : ℂ),
      Measurable (fun ν : Measure ℂ => leastSupersolution ν 1 z t x)) :
    ClusterFamilyMeasurabilityStep.{u} := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ z hz
  exact (measurable_cluster_family_of_measurable_leastSupersolution id 1 z (hv z hz)).aemeasurable

end HarmonicBalls
