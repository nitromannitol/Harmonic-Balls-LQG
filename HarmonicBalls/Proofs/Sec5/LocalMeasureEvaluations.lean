import HarmonicBalls.Proofs.Sec1.Locality
import HarmonicBalls.Proofs.Sec6.MeasureEvaluation
import HarmonicBalls.Proofs.Sec5.PotentialMeasurableDecoder
import HarmonicBalls.Proofs.Sec3.OpenLaplacian

/-! # Local measurability of Borel mass evaluations -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped ENNReal

/-- Open-set mass representatives extend to Borel subsets of a finite-mass
open set, without completing the local σ-algebra. -/
theorem exists_local_borel_mass_representative
    {Ω X : Type*} [mΩ : MeasurableSpace Ω] [TopologicalSpace X] [MeasurableSpace X]
    [BorelSpace X] (P : Measure Ω) (m : MeasurableSpace Ω) (μ : Ω → Measure X)
    {B : Set X} (hB : IsOpen B)
    (hopen : ∀ V : Set X, IsOpen V → V ⊆ B →
      ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧ ∀ᵐ ω ∂P, μ ω V = Y ω)
    (hfin : ∀ᵐ ω ∂P, μ ω B ≠ ∞)
    (A : Set X) (hA : MeasurableSet A) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧ ∀ᵐ ω ∂P, μ ω (A ∩ B) = Y ω := by
  classical
  refine MeasurableSpace.induction_on_inter BorelSpace.measurable_eq isPiSystem_isOpen
    (C := fun A _ => ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧
      ∀ᵐ ω ∂P, μ ω (A ∩ B) = Y ω) ?_ ?_ ?_ ?_ A hA
  · exact ⟨fun _ => 0, measurable_const, by simp⟩
  · intro V hV
    exact hopen _ (hV.inter hB) inter_subset_right
  · intro V hV ih
    obtain ⟨Y, hY, hYeq⟩ := ih
    obtain ⟨Z, hZ, hZeq⟩ := hopen B hB Subset.rfl
    refine ⟨fun ω => Z ω - Y ω, hZ.sub hY, ?_⟩
    filter_upwards [hfin, hYeq, hZeq] with ω hω hYω hZω
    have hfin' : μ ω (V ∩ B) ≠ ∞ :=
      ne_top_of_le_ne_top hω (measure_mono inter_subset_right)
    have heq : Vᶜ ∩ B = B \ (V ∩ B) := by ext x; simp [and_comm]
    rw [heq, measure_sdiff inter_subset_right (hV.inter hB.measurableSet).nullMeasurableSet hfin']
    rw [hYω, hZω]
  · intro f hdisj hfm ih
    choose Y hY hYeq using ih
    refine ⟨fun ω => ∑' i : ℕ, Y i ω, Measurable.tsum hY, ?_⟩
    filter_upwards [ae_all_iff.mpr hYeq] with ω hω
    have hdisj' : Pairwise (Function.onFun Disjoint fun i => f i ∩ B) :=
      fun i j hij => (hdisj hij).mono inter_subset_left inter_subset_left
    rw [iUnion_inter, measure_iUnion hdisj' (fun i => (hfm i).inter hB.measurableSet)]
    exact tsum_congr hω

universe u

/-- Locality of LQG open-set masses gives a local representative for the mass
of each Borel set inside a bounded open domain. -/
theorem exists_local_lqg_borel_mass_representative
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (A : Set ℂ) (hA : MeasurableSet A) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[fieldSigmaAlgebra α₀ hC U] Y ∧
      ∀ᵐ ω ∂P, μ ω (A ∩ U) = Y ω := by
  apply exists_local_borel_mass_representative P (fieldSigmaAlgebra α₀ hC U) μ hU
  · intro V hV hVU
    obtain ⟨Y, hY, hYeq⟩ := hloc hGFF hγ hγ2 hα μ hμ V hV
    exact ⟨Y, hY.mono (fieldSigmaAlgebra_mono α₀ hC hVU) le_rfl, hYeq⟩
  · filter_upwards [hμ] with ω hω
    have : IsLocallyFiniteMeasure (μ ω) := hω.isLocallyFiniteMeasure
    obtain ⟨r, hr⟩ := hUb.subset_ball (0 : ℂ)
    exact ne_top_of_le_ne_top measure_ball_ne_top (measure_mono hr)
  · exact hA

/-- Integrals of nonnegative Borel functions against a random measure inherit
local representatives from its measurable-set evaluations. -/
theorem exists_local_lintegral_representative
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (P : Measure Ω) (m : MeasurableSpace Ω) (ν : Ω → Measure X)
    (f : X → ℝ≥0∞) (hf : Measurable f)
    (hν : ∀ A : Set X, MeasurableSet A →
      ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧ ∀ᵐ ω ∂P, ν ω A = Y ω) :
    ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧ ∀ᵐ ω ∂P, (∫⁻ x, f x ∂(ν ω)) = Y ω := by
  classical
  let s : ℕ → SimpleFunc X ℝ≥0∞ := SimpleFunc.eapprox f
  have hex : ∀ n i, ∃ Y : Ω → ℝ≥0∞, Measurable[m] Y ∧
      ∀ᵐ ω ∂P, ν ω (s n ⁻¹' {i}) = Y ω := by
    intro n i
    exact hν _ ((s n).measurableSet_preimage _)
  choose Y hY hYeq using hex
  let Z : Ω → ℝ≥0∞ := fun ω => ⨆ n, ∑ i ∈ (s n).range, i * Y n i ω
  have hZ : Measurable[m] Z := by
    apply Measurable.iSup
    intro n
    exact Finset.measurable_fun_sum _ (fun i _ => (hY n i).const_mul i)
  refine ⟨Z, hZ, ?_⟩
  have hn : ∀ n, ∀ᵐ ω ∂P,
      (s n).lintegral (ν ω) = ∑ i ∈ (s n).range, i * Y n i ω := by
    intro n
    have he : ∀ᵐ ω ∂P, ∀ i ∈ (s n).range,
        ν ω (s n ⁻¹' {i}) = Y n i ω := by
      exact (s n).range.eventually_all.mpr (fun i _ => hYeq n i)
    filter_upwards [he] with ω hω
    simp only [SimpleFunc.lintegral]
    exact Finset.sum_congr rfl (fun i hi => congrArg (i * ·) (hω i hi))
  filter_upwards [ae_all_iff.mpr hn] with ω hω
  rw [lintegral_eq_iSup_eapprox_lintegral hf]
  exact iSup_congr hω

/-- Each fixed Green-potential section on a disc has a representative
measurable with respect to the field on that disc. -/
theorem exists_local_lqg_greenPotentialBall_representative
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) (R : ℝ) (x : ℂ) :
    ∃ Y : Ω → ℝ, Measurable[fieldSigmaAlgebra α₀ hC (ball 0 R)] Y ∧
      ∀ᵐ ω ∂P, greenPotentialBall (μ ω) R x = Y ω := by
  have hg := measurable_greenFunction_ball R x
  obtain ⟨Y, hY, hYeq⟩ := exists_local_lintegral_representative P
    (fieldSigmaAlgebra α₀ hC (ball 0 R)) (fun ω => (μ ω).restrict (ball 0 R))
    (fun y => ENNReal.ofReal (greenFunction (ball 0 R) x y))
    (ENNReal.measurable_ofReal.comp hg) (by
      intro A hA
      obtain ⟨Y, hY, hYeq⟩ := exists_local_lqg_borel_mass_representative hγ hγ2 hα
        hGFF hμ hloc isOpen_ball isBounded_ball A hA
      refine ⟨Y, hY, ?_⟩
      filter_upwards [hYeq] with ω hω
      simpa only [Measure.restrict_apply hA] using hω)
  refine ⟨fun ω => (Y ω).toReal, ENNReal.measurable_toReal.comp hY, ?_⟩
  filter_upwards [hYeq] with ω hω
  have heq : greenPotentialBall (μ ω) R x =
      ∫ y in ball (0 : ℂ) R, greenFunction (ball 0 R) x y ∂(μ ω) := by
    apply integral_congr_ae
    exact Eventually.of_forall (fun y => greenFunction_ball_comm R y x)
  rw [heq, integral_eq_lintegral_of_nonneg_ae
    (Eventually.of_forall (greenFunction_nonneg isBounded_ball x)) hg.aestronglyMeasurable, hω]

/-- The entire continuous disc potential admits a local representative whenever
it is almost surely continuous on the closed disc. -/
theorem exists_local_lqg_greenPotentialBall_continuous_representative
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) {R : ℝ} (hR : 0 < R)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (greenPotentialBall (μ ω) R) (closedBall 0 R)) :
    ∃ Q : Ω → C(closedBall (0 : ℂ) R, ℝ),
      Measurable[fieldSigmaAlgebra α₀ hC (ball 0 R)] Q ∧
      ∀ᵐ ω ∂P, ∀ x, Q ω x = greenPotentialBall (μ ω) R x := by
  classical
  let X := closedBall (0 : ℂ) R
  let : Nonempty X := ⟨⟨0, by change (0 : ℂ) ∈ closedBall 0 R; simpa using hR.le⟩⟩
  let e : ℕ → X := denseSeq X
  let enc : C(X, ℝ) → ℕ → ℝ := fun f n => f (e n)
  have henc : Measurable enc := by
    apply Measurable.of_eval
    intro n
    exact ContinuousMap.measurable_eval (e n)
  have hinj : Function.Injective enc := by
    intro f g hfg
    apply ContinuousMap.ext
    intro x
    have hfun : (f : X → ℝ) = g := (denseRange_denseSeq X).equalizer f.continuous g.continuous (by
      funext n
      exact congrFun hfg n)
    exact congrFun hfun x
  have hemb : MeasurableEmbedding enc := henc.measurableEmbedding hinj
  choose Y hY hYeq using fun n : ℕ =>
    exists_local_lqg_greenPotentialBall_representative hγ hγ2 hα hGFF hμ hloc R (e n)
  let q : Ω → ℕ → ℝ := fun ω n => Y n ω
  have hq : Measurable[fieldSigmaAlgebra α₀ hC (ball 0 R)] q := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC (ball 0 R)
    exact Measurable.of_eval hY
  refine ⟨fun ω => hemb.invFun (q ω), hemb.measurable_invFun.comp hq, ?_⟩
  filter_upwards [hcont, ae_all_iff.mpr hYeq] with ω hc heq
  let f : C(X, ℝ) := ⟨fun x => greenPotentialBall (μ ω) R x, hc.domRestrict⟩
  have hqeq : q ω = enc f := by
    funext n
    exact (heq n).symm
  intro x
  change hemb.invFun (q ω) x = _
  rw [hqeq, hemb.leftInverse_invFun f]
  rfl

/-- For good measures, the shifted odometer at a fixed point is a continuous
function of the continuous Green potential. -/
theorem exists_continuous_shiftedOdometer_decoder
    {R t : ℝ} {z x : ℂ} (hR : 0 < R) (_hz : z ∈ ball (0 : ℂ) R)
    (ht : 0 < t) (hx : x ∈ ball (0 : ℂ) R) (hxz : x ≠ z) :
    ∃ g : C(closedBall (0 : ℂ) R, ℝ) → ℝ, Continuous g ∧
      ∀ ν : Measure ℂ, IsLocallyFiniteMeasure ν →
        (∃ βminus βplus, VolumeGrowth ν R βminus βplus) →
        ∀ q : C(closedBall (0 : ℂ) R, ℝ),
          (∀ y, q y = greenPotentialBall ν R y) → shiftedOdometer ν R z t x = g q := by
  classical
  let A := {ν : Measure ℂ // IsLocallyFiniteMeasure ν ∧
    ∃ βminus βplus, VolumeGrowth ν R βminus βplus}
  obtain ⟨Q, hQ, hQeq⟩ := exists_measurable_greenPotentialBall_decoder hR
  have hcont : ∀ a : A, ContinuousOn (greenPotentialBall a.1 R) (closedBall 0 R) := by
    intro a
    obtain ⟨βminus, βplus, hv⟩ := a.2.2
    exact greenPotentialBallContinuousStep_holds a.1 a.2.1 R βminus βplus hR hv
  have hclass : ∀ a : A, (shiftedSupersolutions a.1 R z t).Nonempty := by
    intro a
    obtain ⟨βminus, βplus, hv⟩ := a.2.2
    refine ⟨greenPotentialBall a.1 R, greenPotentialBall_mem_shiftedSupersolutions
      ht.le (hcont a) ?_⟩
    exact (greenPotentialBallLaplacianStep_holds a.1 a.2.1 R βminus βplus hR hv).laplacianLE
  let q : A → C(closedBall (0 : ℂ) R, ℝ) := fun a => Q a.1
  let f : A → ℝ := fun a => shiftedOdometer a.1 R z t x
  have hdist : ∀ a b, dist (f a) (f b) ≤ (2 : NNReal) * dist (q a) (q b) := by
    intro a b
    rw [Real.dist_eq]
    apply abs_shiftedOdometer_sub_le_of_greenPotentialBall (hclass a) (hclass b) ?_
      (ball_subset_closedBall hx) hxz
    intro y hy
    have h := ContinuousMap.dist_apply_le_dist (f := q a) (g := q b) ⟨y, hy⟩
    simpa only [Real.dist_eq, q, hQeq _ (hcont a), hQeq _ (hcont b)] using h
  obtain ⟨g, hg, hgf⟩ := exists_lipschitz_factor_of_dist_le q f 2 hdist
  refine ⟨g, hg.continuous, ?_⟩
  intro ν hν hv q' hq'
  let a : A := ⟨ν, hν, hv⟩
  have hqeq : q' = q a := by
    ext y
    rw [hq' y, hQeq _ (hcont a)]
  rw [hqeq]
  exact hgf a

/-- A fixed point of a disc cluster is measurable with respect to the field
on the disc, up to an event of probability zero. -/
theorem exists_local_lqg_cluster_membership
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {R t : ℝ} {z x : ℂ} (hR : 0 < R) (hz : z ∈ ball (0 : ℂ) R) (ht : 0 < t) :
    ∃ E : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC (ball 0 R)] E ∧
      {ω | x ∈ cluster (μ ω) R z t} =ᵐ[P] E := by
  classical
  by_cases hx : x ∈ ball (0 : ℂ) R
  · by_cases hxz : x = z
    · refine ⟨univ, MeasurableSet.univ, ?_⟩
      filter_upwards [] with ω
      apply propext
      change x ∈ cluster (μ ω) R z t ↔ True
      exact ⟨fun _ => trivial, fun _ => mem_cluster_iff.mpr ⟨hx, Or.inl hxz⟩⟩
    · obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
      have hcont : ∀ᵐ ω ∂P, ContinuousOn (greenPotentialBall (μ ω) R) (closedBall 0 R) := by
        filter_upwards [hae] with ω hω
        exact greenPotentialBallContinuousStep_holds _ hω.1 R βm βp hR (hω.2 R hR)
      obtain ⟨Q, hQ, hQeq⟩ := exists_local_lqg_greenPotentialBall_continuous_representative
        hγ hγ2 hα hGFF hμ hloc hR hcont
      obtain ⟨g, hg, hgood⟩ := exists_continuous_shiftedOdometer_decoder hR hz ht hx hxz
      refine ⟨{ω | 0 < g (Q ω)}, measurableSet_lt measurable_const (hg.measurable.comp hQ), ?_⟩
      filter_upwards [hae, hQeq] with ω hω hqω
      have heq := (obstacleCompatibilityShiftStep_holds (μ ω) hω.1 R βm βp hR
        (hω.2 R hR) z hz t ht).2.2.1
      have hgfeq := hgood (μ ω) hω.1 ⟨βm, βp, hω.2 R hR⟩ (Q ω) hqω
      apply propext
      rw [heq, mem_nonCoincidenceSet_iff]
      simp only [hx, hxz, false_or, true_and, hgfeq]
  · refine ⟨∅, @MeasurableSet.empty Ω (fieldSigmaAlgebra α₀ hC (ball 0 R)), ?_⟩
    filter_upwards [] with ω
    apply propext
    change x ∈ cluster (μ ω) R z t ↔ False
    exact ⟨fun h => hx (mem_cluster_iff.mp h).1, False.elim⟩

/-- For an open set, containment of its closure in a closed disc is detected
by its intersections with a fixed countable dense sequence. -/
theorem closure_subset_closedBall_iff_denseSeq {V : Set ℂ} (hV : IsOpen V) (s : ℝ) :
    closure V ⊆ closedBall (0 : ℂ) s ↔
      ∀ n, denseSeq ℂ n ∈ V → denseSeq ℂ n ∈ closedBall (0 : ℂ) s := by
  constructor
  · intro h n hn
    exact h (subset_closure hn)
  · intro h
    rw [closure_eq_closure_inter_denseSeq hV]
    apply closure_minimal _ isClosed_closedBall
    rintro x ⟨hx, n, rfl⟩
    exact h n hx

/-- For a fixed disc cluster, containment of its closure in a closed disc is
a local event, up to a null set. -/
theorem exists_local_lqg_cluster_closedBall_containment
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {R t : ℝ} {z : ℂ} (hR : 0 < R) (hz : z ∈ ball (0 : ℂ) R) (ht : 0 < t)
    (s : ℝ) :
    ∃ E : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC (ball 0 R)] E ∧
      {ω | closure (cluster (μ ω) R z t) ⊆ closedBall (0 : ℂ) s} =ᵐ[P] E := by
  classical
  choose E hE hEq using fun n : ℕ =>
    exists_local_lqg_cluster_membership hI2 hγ hγ2 hα hGFF hμ hloc hR hz ht (x := denseSeq ℂ n)
  let F : Set Ω := ⋂ n, (E n)ᶜ ∪ if denseSeq ℂ n ∈ closedBall (0 : ℂ) s then univ else ∅
  have hF : MeasurableSet[fieldSigmaAlgebra α₀ hC (ball 0 R)] F := by
    apply MeasurableSet.iInter
    intro n
    exact (hE n).compl.union (by split_ifs <;> simp)
  refine ⟨F, hF, ?_⟩
  filter_upwards [ae_all_iff.mpr hEq,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω heq hopen
  have hop := (hopen t R ht hR z hz).1
  apply propext
  rw [closure_subset_closedBall_iff_denseSeq hop]
  simp only [F, mem_iInter, mem_union, mem_compl_iff]
  constructor
  · intro h n
    by_cases hs : denseSeq ℂ n ∈ closedBall (0 : ℂ) s
    · right
      simp [hs]
    · left
      intro hn
      exact hs (h n ((propext_iff.mp (heq n)).mpr hn))
  · intro h n hn
    have hnE := (propext_iff.mp (heq n)).mp hn
    rcases h n with hnot | hmem
    · exact (hnot hnE).elim
    · by_contra hs
      simp [hs] at hmem

/-- Compact containment in an open disc is detected by countably many
concentric closed discs. -/
theorem compact_subset_ball_iff_closedBall_exhaustion
    {K : Set ℂ} (hK : IsCompact K) {R : ℝ} :
    K ⊆ ball (0 : ℂ) R ↔ ∃ n : ℕ, K ⊆ closedBall 0 (R - 1 / ((n : ℝ) + 1)) := by
  constructor
  · intro hsub
    by_cases hne : K.Nonempty
    · obtain ⟨x, hx, hmax⟩ := hK.exists_isMaxOn hne (continuous_id.dist continuous_const).continuousOn
      have hlt : dist x (0 : ℂ) < R := hsub hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hlt)
      refine ⟨n, ?_⟩
      intro y hy
      change dist y (0 : ℂ) ≤ R - 1 / ((n : ℝ) + 1)
      have hymax : dist y (0 : ℂ) ≤ dist x (0 : ℂ) := hmax hy
      linarith
    · refine ⟨0, ?_⟩
      exact Set.not_nonempty_iff_eq_empty.mp hne ▸ empty_subset _
  · rintro ⟨n, hn⟩
    apply hn.trans (closedBall_subset_ball ?_)
    have hpos : 0 < (1 : ℝ) / ((n : ℝ) + 1) := by positivity
    linarith

/-- Compact containment of a disc cluster in its own domain is a local event.
In particular this gives the unit-disc containment event used in Section 5. -/
theorem exists_local_lqg_cluster_ball_containment
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {R t : ℝ} {z : ℂ} (hR : 0 < R) (hz : z ∈ ball (0 : ℂ) R) (ht : 0 < t) :
    ∃ E : Set Ω, MeasurableSet[fieldSigmaAlgebra α₀ hC (ball 0 R)] E ∧
      {ω | closure (cluster (μ ω) R z t) ⊆ ball (0 : ℂ) R} =ᵐ[P] E := by
  classical
  choose E hE hEq using fun n : ℕ =>
    exists_local_lqg_cluster_closedBall_containment hI2 hγ hγ2 hα hGFF hμ hloc hR hz ht
      (R - 1 / ((n : ℝ) + 1))
  refine ⟨⋃ n, E n, MeasurableSet.iUnion hE, ?_⟩
  filter_upwards [ae_all_iff.mpr hEq] with ω heq
  have hcl : closure (cluster (μ ω) R z t) ⊆ closedBall (0 : ℂ) R := by
    apply closure_minimal _ isClosed_closedBall
    intro x hx
    exact ball_subset_closedBall (mem_cluster_iff.mp hx).1
  have hk : IsCompact (closure (cluster (μ ω) R z t)) :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure hcl
  apply propext
  rw [compact_subset_ball_iff_closedBall_exhaustion hk]
  simp only [mem_iUnion]
  exact exists_congr (fun n => propext_iff.mp (heq n))

end HarmonicBalls
