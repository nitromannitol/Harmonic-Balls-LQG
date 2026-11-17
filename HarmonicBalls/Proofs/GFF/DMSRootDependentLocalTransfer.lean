import HarmonicBalls.Proofs.GFF.DMSInsertedLocalAbsoluteContinuity
import HarmonicBalls.Proofs.Sec8.MeanZeroDistributionVersion
import HarmonicBalls.Proofs.Sec8.TranslatedDistributionInsertion
import HarmonicBalls.Proofs.Sec8.PhaseTorusLebesgue
import HarmonicBalls.Proofs.Sec8.UniformSingularPhaseCertificate
import HarmonicBalls.Proofs.GFF.LogInsertionReconstruction
import HarmonicBalls.FirstPass.S8c.TailTransfer
import HarmonicBalls.Proofs.Sec8.JointVeryGoodAE

/-!
# Root-dependent local event transfer

A measurable marked event with local sections transfers from the field with a
root insertion to almost every root of the singular Liouville measure.
-/

noncomputable section

open MeasureTheory Set Metric Filter

namespace HarmonicBalls

/-- Restrict global mean-zero test pairings to a local region. -/
def restrictGlobalPairings (U : Set ℂ) (v : ModConstTestPairings univ) :
    ModConstTestPairings U := fun φ =>
  v ⟨φ.1, ⟨φ.2.1.1, φ.2.1.2.1, subset_univ _⟩, φ.2.2⟩

/-- A jointly measurable marked event whose sections are measurable local events
holds at almost every singular-measure root if its sections hold for the
whole-plane field with the corresponding root insertion. -/
theorem IsWholePlaneGFF.ae_singular_root_local_of_reference
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α < lqgQ γ) (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (S : Set (ModConstTestPairings univ × ℂ)) (hS : MeasurableSet S)
    (href : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 →
      ∃ r : ℝ, 0 < r ∧ r < ‖z‖ ∧ ‖z‖ + r < 1 ∧
        ∃ E : Set (ModConstTestPairings (ball z r)), MeasurableSet E ∧
          (∀ v, (v, z) ∈ S ↔ restrictGlobalPairings (ball z r) v ∈ E) ∧
          ∀ᵐ ω ∂P, (fun φ => hC ω φ.1 +
            ∫ w, φ.1 w * (-γ * Real.log ‖w - z‖)) ∈ E) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), z ∈ ball (0 : ℂ) 1 →
      (localModConstField α hC univ ω, z) ∈ S := by
  apply hh.ae_singular_local_marked_of_ae_shifted hγ hγ2 hα hμ hν univ S hS
  filter_upwards [href] with z hz hzball
  obtain ⟨r, hr, hrz, hrunit, E, hE, hlocal, hgood⟩ := hz hzball
  let A : Ω → ModConstTestPairings (ball z r) := fun ω =>
    localModConstField α (fun _ : Unit => shiftedPairing γ z (hC ω)) (ball z r) ()
  let B : Ω → ModConstTestPairings (ball z r) := fun ω φ =>
    hC ω φ.1 + ∫ w, φ.1 w * (-γ * Real.log ‖w - z‖)
  have hAm : Measurable A := by
    apply measurable_pi_iff.mpr
    intro φ
    change Measurable fun ω => (hC ω φ.1 + ∫ w, dmsShift γ z w * φ.1 w) -
      α * ∫ x, φ.1 x * Real.log ‖x‖
    exact ((hh.measurable_pairing φ.1 ⟨φ.2.1.1, φ.2.1.2.1, subset_univ _⟩).add_const _).sub_const _
  have hBm : Measurable B := by
    apply measurable_pi_iff.mpr
    intro φ
    exact (hh.measurable_pairing φ.1 ⟨φ.2.1.1, φ.2.1.2.1, subset_univ _⟩).add_const _
  have hab : P.map A ≪ P.map B :=
    (hh.inserted_marked_local_law_equivalence_of_radius α γ hr hrz hrunit).1
  have hB : ∀ᵐ v ∂(P.map B), v ∈ E := (ae_map_iff hBm.aemeasurable hE).2 hgood
  have hA : ∀ᵐ ω ∂P, A ω ∈ E := (ae_map_iff hAm.aemeasurable hE).1 (hab.ae_le hB)
  filter_upwards [hA] with ω hω
  apply (hlocal _).2
  exact hω

end HarmonicBalls

open MeasureTheory Set TopologicalSpace
open scoped Distributions
namespace HarmonicBalls

/-- Form a mean-zero local test by subtracting its integral times a unit-mass test. -/
def localGaugeTest (U : Opens ℂ) (ρ χ : LQGMetric.TestOn U)
    (hρ : ∫ x, ρ x = 1) : {φ : ℂ → ℝ // IsTestFunction U φ ∧ ∫ x, φ x = 0} := by
  let ψ : LQGMetric.TestOn U := χ - (∫ x, χ x) • ρ
  let ψ' : LQGMetric.TestC := LQGMetric.MarkovGerm.extC U ψ
  refine ⟨ψ', ⟨⟨ψ'.contDiff, ψ'.hasCompactSupport.isCompact, ?_⟩, ?_⟩⟩
  · simpa [ψ', LQGMetric.MarkovGerm.coe_extC] using ψ.tsupport_subset
  · simp only [ψ', LQGMetric.MarkovGerm.coe_extC]
    change ∫ x, (χ x - (∫ y, χ y) * ρ x) = 0
    rw [integral_sub (χ.continuous.integrable_of_hasCompactSupport χ.hasCompactSupport)
      ((ρ.continuous.integrable_of_hasCompactSupport ρ.hasCompactSupport).const_mul _),
      integral_const_mul, hρ, mul_one, sub_self]

/-- Reconstruct a distribution on an open set from its local mean-zero pairings. -/
def localGaugeVersion (U : Opens ℂ) (ρ : LQGMetric.TestOn U)
    (hρ : ∫ x, ρ x = 1) (v : ModConstTestPairings U) : LQGMetric.DistOn U :=
  LQGMetric.pairJInv U (fun c => v (localGaugeTest U ρ (LQGMetric.comb U c) hρ))

/-- Local reconstruction is measurable for the cylinder sigma-algebra. -/
theorem measurable_localGaugeVersion (U : Opens ℂ) (ρ : LQGMetric.TestOn U)
    (hρ : ∫ x, ρ x = 1) : Measurable (localGaugeVersion U ρ hρ) := by
  apply (LQGMetric.measurable_pairJInv U).comp
  exact measurable_pi_iff.mpr fun c => measurable_pi_apply _

/-- Reconstructing the local pairings of a distribution fixes its gauge locally. -/
theorem localGaugeVersion_pairings (U : Opens ℂ) (ρ : LQGMetric.TestOn U)
    (hρ : ∫ x, ρ x = 1) (h : LQGMetric.DistC) :
    localGaugeVersion U ρ hρ (fun φ => h ⟨φ.1, φ.2.1.1, φ.2.1.2.1, subset_univ _⟩) =
      LQGMetric.restrictTo U (LQGMetric.addConst h (-(h (LQGMetric.MarkovGerm.extC U ρ)))) := by
  unfold localGaugeVersion
  rw [show (fun c => h ⟨(localGaugeTest U ρ (LQGMetric.comb U c) hρ).1,
      (localGaugeTest U ρ (LQGMetric.comb U c) hρ).2.1.1,
      (localGaugeTest U ρ (LQGMetric.comb U c) hρ).2.1.2.1, subset_univ _⟩) =
    LQGMetric.pairJ U (LQGMetric.restrictTo U
      (LQGMetric.addConst h (-(h (LQGMetric.MarkovGerm.extC U ρ))))) by
    funext c
    change h (LQGMetric.MarkovGerm.extC U (LQGMetric.comb U c -
      (∫ x, LQGMetric.comb U c x) • ρ)) = _
    change _ = LQGMetric.addConst h (-(h (LQGMetric.MarkovGerm.extC U ρ)))
      (LQGMetric.MarkovGerm.extC U (LQGMetric.comb U c))
    rw [map_sub, map_smul, map_sub, map_smul, LQGMetric.GFFInv.addConst_apply]
    simp only [smul_eq_mul, LQGMetric.MarkovGerm.coe_extC]
    ring]
  exact LQGMetric.pairJInv_pairJ U _

/-- Local reconstruction preserves every mean-zero pairing of a distribution. -/
theorem localGaugeVersion_apply (U : Opens ℂ) (ρ : LQGMetric.TestOn U)
    (hρ : ∫ x, ρ x = 1) (h : LQGMetric.DistC) (φ : LQGMetric.TestOn U)
    (hφ : ∫ x, φ x = 0) :
    localGaugeVersion U ρ hρ (fun ψ => h ⟨ψ.1, ψ.2.1.1, ψ.2.1.2.1, subset_univ _⟩) φ =
      h (LQGMetric.MarkovGerm.extC U φ) := by
  rw [localGaugeVersion_pairings]
  change LQGMetric.addConst h (-(h (LQGMetric.MarkovGerm.extC U ρ)))
    (LQGMetric.MarkovGerm.extC U φ) = _
  rw [LQGMetric.GFFInv.addConst_apply]
  simp only [LQGMetric.MarkovGerm.coe_extC, hφ, zero_mul, add_zero]

end HarmonicBalls

namespace HarmonicBalls

/-- Local reconstruction can be paired jointly measurably with a continuous
family of local test functions. -/
theorem measurable_localGaugeVersion_family
    {X : Type*} [TopologicalSpace X] [MetrizableSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [OpensMeasurableSpace X]
    (U : Opens ℂ) (ρ : LQGMetric.TestOn U) (hρ : ∫ x, ρ x = 1)
    (χ : X → LQGMetric.TestOn U) (hχ : Continuous χ) :
    Measurable (fun p : ModConstTestPairings U × X =>
      localGaugeVersion U ρ hρ p.1 (χ p.2)) := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (x : X) (v : ModConstTestPairings U) => localGaugeVersion U ρ hρ v (χ x))
    (fun v => (map_continuous (localGaugeVersion U ρ hρ v)).comp hχ)
    (fun x => (LQGMetric.measurable_distOn_apply (χ x)).comp
      (measurable_localGaugeVersion U ρ hρ))
  exact h.comp measurable_swap

/-- A translated test, restricted to a common compact buffer in the local region. -/
def localTranslatedTest (U : Opens ℂ) (K : Compacts ℂ) (hKU : (K : Set ℂ) ⊆ U)
    (c : ℂ) (δ : ℝ) (φ : LQGMetric.TestC0)
    (hK : ∀ z : closedBall c δ, ∀ y ∉ (K : Set ℂ), φ.1 (y - z) = 0)
    (z : closedBall c δ) : LQGMetric.TestOn U :=
  TestFunction.ofSupportedIn hKU (LQGMetric.testFamK K
    (fun z : closedBall c δ => fun y => φ.1 (y - z))
    (fun _ => φ.1.contDiff.comp (contDiff_id.sub contDiff_const)) hK z)

/-- Buffered translations form a continuous family of local tests. -/
theorem continuous_localTranslatedTest
    (U : Opens ℂ) (K : Compacts ℂ) (hKU : (K : Set ℂ) ⊆ U)
    (c : ℂ) (δ : ℝ) (φ : LQGMetric.TestC0)
    (hK : ∀ z : closedBall c δ, ∀ y ∉ (K : Set ℂ), φ.1 (y - z) = 0) :
    Continuous (localTranslatedTest U K hKU c δ φ hK) := by
  let : CompactSpace (closedBall c δ) := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  have hD : ∀ i : ℕ, Continuous fun p : (closedBall c δ) × ℂ =>
      iteratedFDeriv ℝ i (fun y => φ.1 (y - p.1)) p.2 := by
    intro i
    simp_rw [sub_eq_add_neg, iteratedFDeriv_comp_add_right]
    exact (φ.1.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      (continuous_snd.add (continuous_subtype_val.comp continuous_fst).neg)
  exact (TestFunction.continuous_ofSupportedIn hKU).comp
    (LQGMetric.continuous_testFamK K _ _ hK hD)

/-- The buffered translated local test has integral zero. -/
theorem integral_localTranslatedTest
    (U : Opens ℂ) (K : Compacts ℂ) (hKU : (K : Set ℂ) ⊆ U)
    (c : ℂ) (δ : ℝ) (φ : LQGMetric.TestC0)
    (hK : ∀ z : closedBall c δ, ∀ y ∉ (K : Set ℂ), φ.1 (y - z) = 0)
    (z : closedBall c δ) : ∫ y, localTranslatedTest U K hKU c δ φ hK z y = 0 := by
  change (∫ y, φ.1 (y - z)) = 0
  rw [integral_sub_right_eq_self]
  exact φ.2

/-- Local pairings determine translated mean-zero distribution pairings at
all roots in a common compact buffer, jointly measurably in field and root. -/
theorem measurable_localTranslated_pairing
    (U : Opens ℂ) (ρ : LQGMetric.TestOn U) (hρ : ∫ x, ρ x = 1)
    (K : Compacts ℂ) (hKU : (K : Set ℂ) ⊆ U)
    (c : ℂ) (δ : ℝ) (φ : LQGMetric.TestC0)
    (hK : ∀ z : closedBall c δ, ∀ y ∉ (K : Set ℂ), φ.1 (y - z) = 0) :
    Measurable (fun p : ModConstTestPairings U × closedBall c δ =>
      localGaugeVersion U ρ hρ p.1 (localTranslatedTest U K hKU c δ φ hK p.2)) :=
  measurable_localGaugeVersion_family U ρ hρ _ (continuous_localTranslatedTest U K hKU c δ φ hK)

/-- The translated local reconstruction agrees with the translated global
pairing for every distribution and every root in the buffer. -/
theorem localTranslated_pairing_eq
    (U : Opens ℂ) (ρ : LQGMetric.TestOn U) (hρ : ∫ x, ρ x = 1)
    (K : Compacts ℂ) (hKU : (K : Set ℂ) ⊆ U)
    (c : ℂ) (δ : ℝ) (φ : LQGMetric.TestC0)
    (hK : ∀ z : closedBall c δ, ∀ y ∉ (K : Set ℂ), φ.1 (y - z) = 0)
    (h : LQGMetric.DistC) (z : closedBall c δ) :
    localGaugeVersion U ρ hρ
        (fun ψ => h ⟨ψ.1, ψ.2.1.1, ψ.2.1.2.1, subset_univ _⟩)
        (localTranslatedTest U K hKU c δ φ hK z) =
      h (LQGMetric.testAffinePull 1 z φ.1) := by
  rw [localGaugeVersion_apply U ρ hρ h _ (integral_localTranslatedTest U K hKU c δ φ hK z)]
  congr 1
  ext y
  simp [localTranslatedTest, LQGMetric.testFamK, LQGMetric.testAffinePull_apply]
  rfl

/-- Every nonempty open set carries a compactly supported smooth unit-mass test. -/
theorem exists_local_unitMass_test (U : Opens ℂ) (hU : (U : Set ℂ).Nonempty) :
    ∃ ρ : LQGMetric.TestOn U, ∫ x, ρ x = 1 := by
  obtain ⟨z, hz⟩ := hU
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp U.2 z hz
  let b : ContDiffBump z := ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  refine ⟨⟨b.normed volume, b.contDiff_normed, b.hasCompactSupport_normed, ?_⟩,
    b.integral_normed⟩
  rw [b.tsupport_normed_eq]
  exact (closedBall_subset_ball (by dsimp [b]; linarith)).trans hball

/-- Translates of a test supported in a disk stay inside the sum-radius disk
when their centres lie in a closed disk. -/
theorem translated_test_eq_zero_outside_closedBall
    (c : ℂ) (δ r : ℝ) (φ : LQGMetric.TestC0)
    (hφ : tsupport (φ.1 : ℂ → ℝ) ⊆ closedBall 0 r)
    (z : closedBall c δ) (y : ℂ) (hy : y ∉ closedBall c (δ + r)) :
    φ.1 (y - z) = 0 := by
  by_contra hne
  have hb : ‖y - (z : ℂ)‖ ≤ r := by
    have hm := hφ (subset_closure hne)
    simpa only [mem_closedBall, dist_zero_right] using hm
  have hz : ‖(z : ℂ) - c‖ ≤ δ := by
    simpa only [mem_closedBall, dist_eq_norm] using z.2
  have hy' : δ + r < ‖y - c‖ := by
    simpa only [mem_closedBall, not_le, dist_eq_norm] using hy
  have ht : ‖y - c‖ ≤ ‖y - (z : ℂ)‖ + ‖(z : ℂ) - c‖ := by
    calc
      ‖y - c‖ = ‖(y - (z : ℂ)) + ((z : ℂ) - c)‖ := by congr 1; ring
      _ ≤ _ := norm_add_le _ _
  linarith

/-- Recenter every local mean-zero pairing using one buffered chart. -/
def localTranslatedObservation
    (U : Opens ℂ) (ρ : LQGMetric.TestOn U) (hρ : ∫ x, ρ x = 1)
    (c : ℂ) (δ r : ℝ) (hKU : closedBall c (δ + r) ⊆ U)
    (p : ModConstTestPairings U × closedBall c δ) :
    Section6.LocalTest (ball 0 r) → ℝ :=
  fun φ =>
    localGaugeVersion U ρ hρ p.1
      (localTranslatedTest U ⟨closedBall c (δ + r), isCompact_closedBall _ _⟩
        hKU c δ φ.1 (translated_test_eq_zero_outside_closedBall c δ r φ.1
          (φ.2.trans ball_subset_closedBall)) p.2)

/-- The buffered recentered local pairing process is jointly measurable in
the local pairings and the centre. -/
theorem measurable_localTranslatedObservation
    (U : Opens ℂ) (ρ : LQGMetric.TestOn U) (hρ : ∫ x, ρ x = 1)
    (c : ℂ) (δ r : ℝ) (hKU : closedBall c (δ + r) ⊆ U) :
    Measurable (localTranslatedObservation U ρ hρ c δ r hKU) := by
  apply measurable_pi_iff.mpr
  intro φ
  exact measurable_localTranslated_pairing U ρ hρ
    ⟨closedBall c (δ + r), isCompact_closedBall _ _⟩ hKU c δ φ.1
      (translated_test_eq_zero_outside_closedBall c δ r φ.1
        (φ.2.trans ball_subset_closedBall))

/-- For the local pairings of a global distribution, the buffered process
is its actual translated pairing process for every root in the chart. -/
theorem localTranslatedObservation_pairings
    (U : Opens ℂ) (ρ : LQGMetric.TestOn U) (hρ : ∫ x, ρ x = 1)
    (c : ℂ) (δ r : ℝ) (hKU : closedBall c (δ + r) ⊆ U)
    (h : LQGMetric.DistC) (z : closedBall c δ) :
    localTranslatedObservation U ρ hρ c δ r hKU
      (fun ψ => h ⟨ψ.1, ψ.2.1.1, ψ.2.1.2.1, subset_univ _⟩, z) =
        fun φ => h (LQGMetric.testAffinePull 1 z φ.1.1) := by
  funext φ
  exact localTranslated_pairing_eq U ρ hρ
    ⟨closedBall c (δ + r), isCompact_closedBall _ _⟩ hKU c δ φ.1
      (translated_test_eq_zero_outside_closedBall c δ r φ.1
        (φ.2.trans ball_subset_closedBall)) h z

/-- A total measurable projection onto a closed root disk, using its centre
outside the disk. -/
def bufferedRoot (c : ℂ) (δ : ℝ) (hδ : 0 ≤ δ) (z : ℂ) : closedBall c δ := by
  classical
  exact ⟨if z ∈ closedBall c δ then z else c, by
    split_ifs with hz
    · exact hz
    · exact mem_closedBall_self hδ⟩

/-- The total root projection is measurable. -/
theorem measurable_bufferedRoot (c : ℂ) (δ : ℝ) (hδ : 0 ≤ δ) :
    Measurable (bufferedRoot c δ hδ) := by
  classical
  apply Measurable.subtype_mk
  change Measurable (fun z : ℂ => if z ∈ closedBall c δ then z else c)
  exact measurable_id.ite measurableSet_closedBall measurable_const

/-- Restriction to local mean-zero pairings is measurable. -/
theorem measurable_restrictGlobalPairings (U : Set ℂ) :
    Measurable (restrictGlobalPairings U) := by
  exact measurable_pi_iff.mpr fun _ => measurable_pi_apply _

/-- A marked event on one buffered chart, expressed through local pairings. -/
def bufferedLocalEvent
    {T : Type*} (θ : ℂ → T) (U : Opens ℂ) (ρ : LQGMetric.TestOn U)
    (hρ : ∫ x, ρ x = 1) (c : ℂ) (δ r : ℝ) (hδ : 0 ≤ δ)
    (hKU : closedBall c (δ + r) ⊆ U)
    (E : Set (T × (Section6.LocalTest (ball 0 r) → ℝ))) :
    Set (ModConstTestPairings univ × ℂ) :=
  {p | p.2 ∈ closedBall c δ ∧
    (θ p.2, localTranslatedObservation U ρ hρ c δ r hKU
      (restrictGlobalPairings U p.1, bufferedRoot c δ hδ p.2)) ∈ E}

/-- A measurable phase event gives a jointly measurable marked chart event. -/
theorem measurableSet_bufferedLocalEvent
    {T : Type*} [MeasurableSpace T] (θ : ℂ → T) (hθ : Measurable θ)
    (U : Opens ℂ) (ρ : LQGMetric.TestOn U) (hρ : ∫ x, ρ x = 1)
    (c : ℂ) (δ r : ℝ) (hδ : 0 ≤ δ)
    (hKU : closedBall c (δ + r) ⊆ U)
    (E : Set (T × (Section6.LocalTest (ball 0 r) → ℝ))) (hE : MeasurableSet E) :
    MeasurableSet (bufferedLocalEvent θ U ρ hρ c δ r hδ hKU E) := by
  have hm : Measurable (fun p : ModConstTestPairings univ × ℂ =>
      localTranslatedObservation U ρ hρ c δ r hKU
        (restrictGlobalPairings U p.1, bufferedRoot c δ hδ p.2)) :=
    (measurable_localTranslatedObservation U ρ hρ c δ r hKU).comp
      (((measurable_restrictGlobalPairings U).comp measurable_fst).prodMk
        ((measurable_bufferedRoot c δ hδ).comp measurable_snd))
  exact (measurableSet_closedBall.preimage measurable_snd).inter
    (hE.preimage ((hθ.comp measurable_snd).prodMk hm))

/-- Every section of a chart event at a root in the chart is a measurable
event of the local pairings, for all cylinder inputs. -/
theorem bufferedLocalEvent_section
    {T : Type*} [MeasurableSpace T] (θ : ℂ → T)
    (U : Opens ℂ) (ρ : LQGMetric.TestOn U) (hρ : ∫ x, ρ x = 1)
    (c : ℂ) (δ r : ℝ) (hδ : 0 ≤ δ)
    (hKU : closedBall c (δ + r) ⊆ U)
    (E : Set (T × (Section6.LocalTest (ball 0 r) → ℝ))) (hE : MeasurableSet E)
    (z : ℂ) (hz : z ∈ closedBall c δ) :
    ∃ F : Set (ModConstTestPairings U), MeasurableSet F ∧
      ∀ v, (v, z) ∈ bufferedLocalEvent θ U ρ hρ c δ r hδ hKU E ↔
        restrictGlobalPairings U v ∈ F := by
  let F : Set (ModConstTestPairings U) :=
    {v | (θ z, localTranslatedObservation U ρ hρ c δ r hKU (v, ⟨z, hz⟩)) ∈ E}
  have hF : MeasurableSet F :=
    hE.preimage (measurable_const.prodMk
      ((measurable_localTranslatedObservation U ρ hρ c δ r hKU).comp
        (measurable_id.prodMk measurable_const)))
  refine ⟨F, hF, ?_⟩
  intro v
  have he : bufferedRoot c δ hδ z = ⟨z, hz⟩ := by
    classical
    apply Subtype.ext
    change (if z ∈ closedBall c δ then z else c) = z
    split_ifs
    rfl
  change (z ∈ closedBall c δ ∧ (θ z, localTranslatedObservation U ρ hρ c δ r hKU
    (restrictGlobalPairings U v, bufferedRoot c δ hδ z)) ∈ E) ↔ _
  rw [he]
  simp only [hz, true_and, F, mem_ofPred_eq]

/-- On global distribution pairings, the marked chart event is the event
applied to the actual translated local pairing process. -/
theorem bufferedLocalEvent_pairings
    {T : Type*} (θ : ℂ → T)
    (U : Opens ℂ) (ρ : LQGMetric.TestOn U) (hρ : ∫ x, ρ x = 1)
    (c : ℂ) (δ r : ℝ) (hδ : 0 ≤ δ)
    (hKU : closedBall c (δ + r) ⊆ U)
    (E : Set (T × (Section6.LocalTest (ball 0 r) → ℝ)))
    (h : LQGMetric.DistC) (z : ℂ) (hz : z ∈ closedBall c δ) :
    ((fun ψ : {φ : ℂ → ℝ // IsTestFunction univ φ ∧ ∫ x, φ x = 0} =>
      h ⟨ψ.1, ψ.2.1.1, ψ.2.1.2.1, subset_univ _⟩), z) ∈
        bufferedLocalEvent θ U ρ hρ c δ r hδ hKU E ↔
    (θ z, fun φ => h (LQGMetric.testAffinePull 1 z φ.1.1)) ∈ E := by
  have he : bufferedRoot c δ hδ z = ⟨z, hz⟩ := by
    classical
    apply Subtype.ext
    change (if z ∈ closedBall c δ then z else c) = z
    split_ifs
    rfl
  change (z ∈ closedBall c δ ∧ (θ z, localTranslatedObservation U ρ hρ c δ r hKU
    (restrictGlobalPairings U
      (fun ψ => h ⟨ψ.1, ψ.2.1.1, ψ.2.1.2.1, subset_univ _⟩),
      bufferedRoot c δ hδ z)) ∈ E) ↔ _
  rw [he]
  change (z ∈ closedBall c δ ∧ (θ z, localTranslatedObservation U ρ hρ c δ r hKU
    (fun ψ => h ⟨ψ.1, ψ.2.1.1, ψ.2.1.2.1, subset_univ _⟩, ⟨z, hz⟩)) ∈ E) ↔ _
  rw [localTranslatedObservation_pairings]
  exact and_iff_right hz

/-- Restrict mean-zero pairings from a larger local region to a smaller one. -/
def restrictLocalPairings {U V : Set ℂ} (hUV : U ⊆ V)
    (v : ModConstTestPairings V) : ModConstTestPairings U :=
  fun φ => v ⟨φ.1, ⟨φ.2.1.1, φ.2.1.2.1, φ.2.1.2.2.trans hUV⟩, φ.2.2⟩

/-- Restriction between local pairing spaces is measurable. -/
theorem measurable_restrictLocalPairings {U V : Set ℂ} (hUV : U ⊆ V) :
    Measurable (restrictLocalPairings hUV) :=
  measurable_pi_iff.mpr fun _ => measurable_pi_apply _

/-- A chart section factors through any larger region containing the chart. -/
theorem bufferedLocalEvent_section_of_subset
    {T : Type*} [MeasurableSpace T] (θ : ℂ → T)
    (U : Opens ℂ) (ρ : LQGMetric.TestOn U) (hρ : ∫ x, ρ x = 1)
    (c : ℂ) (δ r : ℝ) (hδ : 0 ≤ δ)
    (hKU : closedBall c (δ + r) ⊆ U)
    (E : Set (T × (Section6.LocalTest (ball 0 r) → ℝ))) (hE : MeasurableSet E)
    (z : ℂ) (hz : z ∈ closedBall c δ) (V : Set ℂ) (hUV : (U : Set ℂ) ⊆ V) :
    ∃ F : Set (ModConstTestPairings V), MeasurableSet F ∧
      ∀ v, (v, z) ∈ bufferedLocalEvent θ U ρ hρ c δ r hδ hKU E ↔
        restrictGlobalPairings V v ∈ F := by
  obtain ⟨F, hF, heq⟩ := bufferedLocalEvent_section θ U ρ hρ c δ r hδ hKU E hE z hz
  refine ⟨restrictLocalPairings hUV ⁻¹' F,
    hF.preimage (measurable_restrictLocalPairings hUV), ?_⟩
  intro v
  exact heq v

/-- Assemble countably many marked events by selecting the first root chart. -/
def firstChartEvent (A : ℕ → Set ℂ) (S : ℕ → Set (ModConstTestPairings univ × ℂ)) :
    Set (ModConstTestPairings univ × ℂ) :=
  ⋃ n, {p | p.2 ∈ disjointed A n} ∩ S n

/-- Countable first-chart assembly preserves joint measurability. -/
theorem measurableSet_firstChartEvent
    (A : ℕ → Set ℂ) (S : ℕ → Set (ModConstTestPairings univ × ℂ))
    (hA : ∀ n, MeasurableSet (A n)) (hS : ∀ n, MeasurableSet (S n)) :
    MeasurableSet (firstChartEvent A S) :=
  MeasurableSet.iUnion fun n =>
    ((MeasurableSet.disjointed hA n).preimage measurable_snd).inter (hS n)

/-- On a selected chart, the assembled event is exactly that chart event. -/
theorem firstChartEvent_iff
    (A : ℕ → Set ℂ) (S : ℕ → Set (ModConstTestPairings univ × ℂ))
    (n : ℕ) (z : ℂ) (hz : z ∈ disjointed A n) (v : ModConstTestPairings univ) :
    (v, z) ∈ firstChartEvent A S ↔ (v, z) ∈ S n := by
  constructor
  · intro h
    obtain ⟨m, hm, hS⟩ := mem_iUnion.mp h
    have hmn : m = n := by
      by_contra hne
      exact (Set.disjoint_left.mp (disjoint_disjointed A hne)) hm hz
    simpa only [hmn] using hS
  · intro h
    exact mem_iUnion.mpr ⟨n, hz, h⟩

/-- The selected charts cover precisely the union of the original charts. -/
theorem exists_firstChart_of_mem
    (A : ℕ → Set ℂ) (z : ℂ) (hz : z ∈ ⋃ n, A n) :
    ∃ n, z ∈ disjointed A n := by
  have hz' : z ∈ ⋃ n, disjointed A n := by rwa [iUnion_disjointed]
  exact mem_iUnion.mp hz'

/-- A selected chart section remains a local section after countable assembly. -/
theorem firstChartEvent_section
    (A : ℕ → Set ℂ) (S : ℕ → Set (ModConstTestPairings univ × ℂ))
    (n : ℕ) (z : ℂ) (hz : z ∈ disjointed A n) (V : Set ℂ)
    (hlocal : ∃ F : Set (ModConstTestPairings V), MeasurableSet F ∧
      ∀ v, (v, z) ∈ S n ↔ restrictGlobalPairings V v ∈ F) :
    ∃ F : Set (ModConstTestPairings V), MeasurableSet F ∧
      ∀ v, (v, z) ∈ firstChartEvent A S ↔ restrictGlobalPairings V v ∈ F := by
  obtain ⟨F, hF, heq⟩ := hlocal
  exact ⟨F, hF, fun v => (firstChartEvent_iff A S n z hz v).trans (heq v)⟩

/-- Centre of a chart indexed by a pair of natural numbers. -/
def bufferedChartCenter (u : ℕ → ℂ) (n : ℕ) : ℂ :=
  u (Nat.unpair n).1

/-- Positive reciprocal scale of a chart indexed by a pair of natural numbers. -/
def bufferedChartScale (n : ℕ) : ℝ :=
  1 / (((Nat.unpair n).2 : ℝ) + 1)

/-- Roots whose chart and local-law disk fit inside the punctured unit disk. -/
def bufferedChartRoots (u : ℕ → ℂ) (n : ℕ) : Set ℂ :=
  ball (bufferedChartCenter u n) (bufferedChartScale n) ∩
    {z | 4 * bufferedChartScale n < ‖z‖ ∧ ‖z‖ + 4 * bufferedChartScale n < 1}

/-- Each root chart is measurable. -/
theorem measurableSet_bufferedChartRoots (u : ℕ → ℂ) (n : ℕ) :
    MeasurableSet (bufferedChartRoots u n) := by
  apply measurableSet_ball.inter
  exact (measurableSet_lt measurable_const measurable_norm).inter
    (measurableSet_lt (measurable_norm.add_const _) measurable_const)

/-- Reciprocal chart scales are strictly positive. -/
theorem bufferedChartScale_pos (n : ℕ) : 0 < bufferedChartScale n := by
  unfold bufferedChartScale
  positivity

/-- Dense chart centres and reciprocal scales cover the punctured unit disk. -/
theorem exists_bufferedChart_of_mem
    (u : ℕ → ℂ) (hu : DenseRange u) (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1)
    (hz0 : z ≠ 0) : ∃ n, z ∈ bufferedChartRoots u n := by
  have hnorm : 0 < ‖z‖ := norm_pos_iff.mpr hz0
  have hunit : ‖z‖ < 1 := by simpa only [mem_ball, dist_zero_right] using hz
  have hε : 0 < min ‖z‖ (1 - ‖z‖) / 4 := by positivity
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  let s : ℝ := 1 / ((n : ℝ) + 1)
  have hs : 0 < s := by dsimp [s]; positivity
  have hsmall : 4 * s < ‖z‖ ∧ ‖z‖ + 4 * s < 1 := by
    have h₁ := min_le_left ‖z‖ (1 - ‖z‖)
    have h₂ := min_le_right ‖z‖ (1 - ‖z‖)
    dsimp [s] at hn ⊢
    constructor <;> linarith
  obtain ⟨w, hw, hw'⟩ := Metric.dense_iff.mp hu z s hs
  obtain ⟨m, rfl⟩ := hw'
  refine ⟨Nat.pair m n, ?_⟩
  have hball : z ∈ ball (u m) s := by simpa only [mem_ball, dist_comm] using hw
  change z ∈ ball (u (Nat.unpair (Nat.pair m n)).1)
    (1 / (((Nat.unpair (Nat.pair m n)).2 : ℝ) + 1)) ∧
    4 * (1 / (((Nat.unpair (Nat.pair m n)).2 : ℝ) + 1)) < ‖z‖ ∧
    ‖z‖ + 4 * (1 / (((Nat.unpair (Nat.pair m n)).2 : ℝ) + 1)) < 1
  simpa only [Nat.unpair_pair] using And.intro hball hsmall

/-- A chart around a root fits in a buffered admissible local-law disk. -/
theorem bufferedChart_geometry
    (c z : ℂ) (s : ℝ) (hs : 0 < s) (hz : z ∈ ball c s)
    (hzero : 4 * s < ‖z‖) (hunit : ‖z‖ + 4 * s < 1) :
    closedBall c (s + s / 2) ⊆ ball c (2 * s) ∧
      ball c (2 * s) ⊆ ball z (4 * s) ∧
      0 < 4 * s ∧ 4 * s < ‖z‖ ∧ ‖z‖ + 4 * s < 1 := by
  refine ⟨closedBall_subset_ball (by linarith), ?_, by positivity, hzero, hunit⟩
  intro y hy
  rw [mem_ball] at hz hy ⊢
  have ht := dist_triangle y c z
  rw [dist_comm c z] at ht
  linarith

/-- The open local-field region associated with a buffered chart. -/
def bufferedChartOpen (u : ℕ → ℂ) (n : ℕ) : Opens ℂ :=
  ⟨ball (bufferedChartCenter u n) (2 * bufferedChartScale n), isOpen_ball⟩

/-- The translated observation buffer fits in its chart region. -/
theorem bufferedChart_buffer (u : ℕ → ℂ) (n : ℕ) :
    closedBall (bufferedChartCenter u n)
      (bufferedChartScale n + bufferedChartScale n / 2) ⊆ bufferedChartOpen u n :=
  closedBall_subset_ball (by have h := bufferedChartScale_pos n; linarith)

/-- Every buffered chart has a unit-mass local test. -/
theorem exists_bufferedChart_gauge (u : ℕ → ℂ) (n : ℕ) :
    ∃ ρ : LQGMetric.TestOn (bufferedChartOpen u n), ∫ x, ρ x = 1 := by
  apply exists_local_unitMass_test
  exact ⟨bufferedChartCenter u n, mem_ball_self (by
    have h := bufferedChartScale_pos n
    positivity)⟩

/-- A fixed unit-mass test for each buffered chart. -/
def bufferedChartGauge (u : ℕ → ℂ) (n : ℕ) : LQGMetric.TestOn (bufferedChartOpen u n) :=
  Classical.choose (exists_bufferedChart_gauge u n)

/-- The chart gauge has unit mass. -/
theorem integral_bufferedChartGauge (u : ℕ → ℂ) (n : ℕ) :
    ∫ x, bufferedChartGauge u n x = 1 :=
  Classical.choose_spec (exists_bufferedChart_gauge u n)

/-- Assemble measurable phase events at the buffered chart radii. -/
def chartedLocalEvent
    {T : Type*} (θ : ℂ → T) (u : ℕ → ℂ)
    (E : ∀ n, Set (T × (Section6.LocalTest (ball 0 (bufferedChartScale n / 2)) → ℝ))) :
    Set (ModConstTestPairings univ × ℂ) :=
  firstChartEvent (bufferedChartRoots u) (fun n =>
    bufferedLocalEvent θ (bufferedChartOpen u n) (bufferedChartGauge u n)
      (integral_bufferedChartGauge u n) (bufferedChartCenter u n) (bufferedChartScale n)
      (bufferedChartScale n / 2) (bufferedChartScale_pos n).le (bufferedChart_buffer u n) (E n))

/-- The countable charted event is jointly measurable. -/
theorem measurableSet_chartedLocalEvent
    {T : Type*} [MeasurableSpace T] (θ : ℂ → T) (hθ : Measurable θ) (u : ℕ → ℂ)
    (E : ∀ n, Set (T × (Section6.LocalTest (ball 0 (bufferedChartScale n / 2)) → ℝ)))
    (hE : ∀ n, MeasurableSet (E n)) :
    MeasurableSet (chartedLocalEvent θ u E) := by
  apply measurableSet_firstChartEvent _ _ (measurableSet_bufferedChartRoots u)
  intro n
  exact measurableSet_bufferedLocalEvent θ hθ (bufferedChartOpen u n)
    (bufferedChartGauge u n) (integral_bufferedChartGauge u n)
    (bufferedChartCenter u n) (bufferedChartScale n) (bufferedChartScale n / 2)
    (bufferedChartScale_pos n).le (bufferedChart_buffer u n) (E n) (hE n)

/-- At every nonzero root inside the unit disk, the assembled event has a
measurable section in a disk admissible for the local-law comparison. -/
theorem chartedLocalEvent_admissible_section
    {T : Type*} [MeasurableSpace T] (θ : ℂ → T) (u : ℕ → ℂ) (hu : DenseRange u)
    (E : ∀ n, Set (T × (Section6.LocalTest (ball 0 (bufferedChartScale n / 2)) → ℝ)))
    (hE : ∀ n, MeasurableSet (E n)) (z : ℂ) (hz : z ∈ ball (0 : ℂ) 1) (hz0 : z ≠ 0) :
    ∃ R : ℝ, 0 < R ∧ R < ‖z‖ ∧ ‖z‖ + R < 1 ∧
      ∃ F : Set (ModConstTestPairings (ball z R)), MeasurableSet F ∧
        ∀ v, (v, z) ∈ chartedLocalEvent θ u E ↔ restrictGlobalPairings (ball z R) v ∈ F := by
  obtain ⟨n, hn⟩ := exists_bufferedChart_of_mem u hu z hz hz0
  have hzunion : z ∈ ⋃ n, bufferedChartRoots u n := mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨n, hn⟩ := exists_firstChart_of_mem (bufferedChartRoots u) z hzunion
  have hzn : z ∈ bufferedChartRoots u n := disjointed_subset _ n hn
  have hgeo := bufferedChart_geometry (bufferedChartCenter u n) z (bufferedChartScale n)
    (bufferedChartScale_pos n) hzn.1 hzn.2.1 hzn.2.2
  refine ⟨4 * bufferedChartScale n, hgeo.2.2.1, hgeo.2.2.2.1, hgeo.2.2.2.2, ?_⟩
  apply firstChartEvent_section (bufferedChartRoots u) _ n z hn (ball z (4 * bufferedChartScale n))
  exact bufferedLocalEvent_section_of_subset θ (bufferedChartOpen u n)
    (bufferedChartGauge u n) (integral_bufferedChartGauge u n)
    (bufferedChartCenter u n) (bufferedChartScale n) (bufferedChartScale n / 2)
    (bufferedChartScale_pos n).le (bufferedChart_buffer u n) (E n) (hE n)
    z (ball_subset_closedBall hzn.1) (ball z (4 * bufferedChartScale n)) hgeo.2.1

/-- On distribution pairings, the selected chart event is the corresponding
phase event of the actual translated distribution. -/
theorem chartedLocalEvent_pairings
    {T : Type*} (θ : ℂ → T) (u : ℕ → ℂ)
    (E : ∀ n, Set (T × (Section6.LocalTest (ball 0 (bufferedChartScale n / 2)) → ℝ)))
    (n : ℕ) (z : ℂ) (hz : z ∈ disjointed (bufferedChartRoots u) n)
    (h : LQGMetric.DistC) :
    ((fun ψ : {φ : ℂ → ℝ // IsTestFunction univ φ ∧ ∫ x, φ x = 0} =>
      h ⟨ψ.1, ψ.2.1.1, ψ.2.1.2.1, subset_univ _⟩), z) ∈ chartedLocalEvent θ u E ↔
    (θ z, fun φ => h (LQGMetric.testAffinePull 1 z φ.1.1)) ∈ E n := by
  have hzn : z ∈ bufferedChartRoots u n := disjointed_subset _ n hz
  apply (firstChartEvent_iff (bufferedChartRoots u) _ n z hz _).trans
  exact bufferedLocalEvent_pairings θ (bufferedChartOpen u n)
    (bufferedChartGauge u n) (integral_bufferedChartGauge u n)
    (bufferedChartCenter u n) (bufferedChartScale n) (bufferedChartScale n / 2)
    (bufferedChartScale_pos n).le (bufferedChart_buffer u n) (E n) h z
    (ball_subset_closedBall hzn.1)

/-- View a local mean-zero test as a global mean-zero test. -/
def globalLocalTest (U : Opens ℂ)
    (φ : {ψ : ℂ → ℝ // IsTestFunction U ψ ∧ ∫ x, ψ x = 0}) :
    LQGMetric.TestC0 :=
  ⟨⟨φ.1, φ.2.1.1, φ.2.1.2.1, subset_univ _⟩, φ.2.2⟩

/-- Agreement on the countable local reconstruction coordinates persists
after adding any distribution. -/
theorem localGaugeVersion_add_of_coordinates
    (U : Opens ℂ) (ρ : LQGMetric.TestOn U) (hρ : ∫ x, ρ x = 1)
    (F : (ℂ → ℝ) → ℝ) (h k : LQGMetric.DistC)
    (hcoords : ∀ c : LQGMetric.CoordJ,
      F (localGaugeTest U ρ (LQGMetric.comb U c) hρ).1 =
        h (globalLocalTest U (localGaugeTest U ρ (LQGMetric.comb U c) hρ)).1) :
    localGaugeVersion U ρ hρ (fun φ => F φ.1 + k (globalLocalTest U φ).1) =
      localGaugeVersion U ρ hρ (fun φ => (h + k) (globalLocalTest U φ).1) := by
  unfold localGaugeVersion
  congr 1
  funext c
  dsimp only
  rw [hcoords c]
  rfl

/-- On one probability-one event, the local reconstruction on every chart
agrees with the canonical global distribution after any distributional insertion. -/
theorem IsWholePlaneGFF.ae_chartGauge_add_of_canonical
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (u : ℕ → ℂ) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (k : LQGMetric.DistC),
      localGaugeVersion (bufferedChartOpen u n) (bufferedChartGauge u n)
          (integral_bufferedChartGauge u n)
          (fun φ => hC ω φ.1 + k (globalLocalTest (bufferedChartOpen u n) φ).1) =
      localGaugeVersion (bufferedChartOpen u n) (bufferedChartGauge u n)
          (integral_bufferedChartGauge u n)
          (fun φ => (meanZeroDistributionVersion (Section6.pairingProc hC ω) + k)
            (globalLocalTest (bufferedChartOpen u n) φ).1) := by
  filter_upwards [ae_all_iff.mpr (fun n : ℕ => ae_all_iff.mpr (fun c : LQGMetric.CoordJ =>
    hh.canonical_distribution_version_pairing
      (globalLocalTest (bufferedChartOpen u n)
        (localGaugeTest (bufferedChartOpen u n) (bufferedChartGauge u n)
          (LQGMetric.comb (bufferedChartOpen u n) c) (integral_bufferedChartGauge u n)))))] with ω hω
  intro n k
  apply localGaugeVersion_add_of_coordinates
  intro c
  exact (hω n c).symm

/-- On one field event, the charted event for raw pairings plus any
distribution agrees with the selected phase event for the translated canonical
distribution plus that insertion, simultaneously for all charts and roots. -/
theorem IsWholePlaneGFF.ae_chartedLocalEvent_add_of_canonical
    {Ω T : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (θ : ℂ → T) (u : ℕ → ℂ)
    (E : ∀ n, Set (T × (Section6.LocalTest (ball 0 (bufferedChartScale n / 2)) → ℝ))) :
    ∀ᵐ ω ∂P, ∀ (n : ℕ) (z : ℂ), z ∈ disjointed (bufferedChartRoots u) n →
      ∀ k : LQGMetric.DistC,
      ((fun ψ : {φ : ℂ → ℝ // IsTestFunction univ φ ∧ ∫ x, φ x = 0} =>
        hC ω ψ.1 + k ⟨ψ.1, ψ.2.1.1, ψ.2.1.2.1, subset_univ _⟩), z) ∈
          chartedLocalEvent θ u E ↔
      (θ z, fun φ => (meanZeroDistributionVersion (Section6.pairingProc hC ω) + k)
        (LQGMetric.testAffinePull 1 z φ.1.1)) ∈ E n := by
  filter_upwards [hh.ae_chartGauge_add_of_canonical u] with ω hω
  intro n z hz k
  have hzn : z ∈ bufferedChartRoots u n := disjointed_subset _ n hz
  have hclosed : z ∈ closedBall (bufferedChartCenter u n) (bufferedChartScale n) :=
    ball_subset_closedBall hzn.1
  have hroot : bufferedRoot (bufferedChartCenter u n) (bufferedChartScale n)
      (bufferedChartScale_pos n).le z = ⟨z, hclosed⟩ := by
    classical
    apply Subtype.ext
    change (if z ∈ closedBall (bufferedChartCenter u n) (bufferedChartScale n)
      then z else bufferedChartCenter u n) = z
    split_ifs
    rfl
  have hobs : localTranslatedObservation (bufferedChartOpen u n) (bufferedChartGauge u n)
      (integral_bufferedChartGauge u n) (bufferedChartCenter u n) (bufferedChartScale n)
      (bufferedChartScale n / 2) (bufferedChart_buffer u n)
      (fun φ => hC ω φ.1 + k (globalLocalTest (bufferedChartOpen u n) φ).1, ⟨z, hclosed⟩) =
      fun φ => (meanZeroDistributionVersion (Section6.pairingProc hC ω) + k)
        (LQGMetric.testAffinePull 1 z φ.1.1) := by
    have heq : localTranslatedObservation (bufferedChartOpen u n) (bufferedChartGauge u n)
        (integral_bufferedChartGauge u n) (bufferedChartCenter u n) (bufferedChartScale n)
        (bufferedChartScale n / 2) (bufferedChart_buffer u n)
        (fun φ => hC ω φ.1 + k (globalLocalTest (bufferedChartOpen u n) φ).1, ⟨z, hclosed⟩) =
      localTranslatedObservation (bufferedChartOpen u n) (bufferedChartGauge u n)
        (integral_bufferedChartGauge u n) (bufferedChartCenter u n) (bufferedChartScale n)
        (bufferedChartScale n / 2) (bufferedChart_buffer u n)
        (fun φ => (meanZeroDistributionVersion (Section6.pairingProc hC ω) + k)
          (globalLocalTest (bufferedChartOpen u n) φ).1, ⟨z, hclosed⟩) := by
      funext φ
      change (localGaugeVersion (bufferedChartOpen u n) (bufferedChartGauge u n)
        (integral_bufferedChartGauge u n) _) _ =
        (localGaugeVersion (bufferedChartOpen u n) (bufferedChartGauge u n)
          (integral_bufferedChartGauge u n) _) _
      rw [hω n k]
    rw [heq]
    exact localTranslatedObservation_pairings (bufferedChartOpen u n) (bufferedChartGauge u n)
      (integral_bufferedChartGauge u n) (bufferedChartCenter u n) (bufferedChartScale n)
      (bufferedChartScale n / 2) (bufferedChart_buffer u n)
      (meanZeroDistributionVersion (Section6.pairingProc hC ω) + k) ⟨z, hclosed⟩
  unfold chartedLocalEvent
  rw [firstChartEvent_iff (bufferedChartRoots u) _ n z hz]
  change (z ∈ closedBall (bufferedChartCenter u n) (bufferedChartScale n) ∧
    (θ z, localTranslatedObservation (bufferedChartOpen u n) (bufferedChartGauge u n)
      (integral_bufferedChartGauge u n) (bufferedChartCenter u n) (bufferedChartScale n)
      (bufferedChartScale n / 2) (bufferedChart_buffer u n)
      (fun φ => hC ω φ.1 + k (globalLocalTest (bufferedChartOpen u n) φ).1,
        bufferedRoot (bufferedChartCenter u n) (bufferedChartScale n)
          (bufferedChartScale_pos n).le z)) ∈ E n) ↔ _
  rw [hroot, hobs]
  exact and_iff_right hclosed

/-- Recentring a logarithmic insertion moves its singularity to the origin. -/
theorem logInsertionDistribution_translated (z : ℂ) (a : ℝ) (φ : LQGMetric.TestC) :
    logInsertionDistribution z a (LQGMetric.testAffinePull 1 z φ) =
      ∫ x, φ x * (a * Real.log ‖x‖) := by
  rw [logInsertionDistribution_apply]
  have ht := integral_add_right_eq_self (μ := volume)
    (fun x : ℂ => φ (x - z) * (a * Real.log ‖x - z‖)) z
  simpa [LQGMetric.testAffinePull_apply] using ht.symm

/-- A Haar-phase event for an origin insertion holds for almost every root
and field after translating the corresponding root insertion. -/
theorem IsWholePlaneGFF.ae_ae_translated_origin_phase
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (a r : ℝ)
    (E : Set (PhaseTorus × (Section6.LocalTest (ball 0 r) → ℝ)))
    (hE : MeasurableSet E)
    (hphase : ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      (p.1, fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (a * Real.log ‖x‖)) ∈ E) :
    ∀ᵐ z ∂(volume : Measure ℂ), ∀ᵐ ω ∂P,
      (phaseTorusOfComplex (-z), fun φ : Section6.LocalTest (ball 0 r) =>
        (meanZeroDistributionVersion (Section6.pairingProc hC ω) + logInsertionDistribution z a)
          (LQGMetric.testAffinePull 1 z φ.1.1)) ∈ E := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let H : Ω → LQGMetric.DistC := fun ω => meanZeroDistributionVersion (Section6.pairingProc hC ω)
  let X : ℂ × Ω → (Section6.LocalTest (ball 0 r) → ℝ) := fun p φ =>
    H p.2 (LQGMetric.testAffinePull 1 p.1 φ.1.1) + ∫ x, φ.1.1 x * (a * Real.log ‖x‖)
  let Y : ℂ × Ω → (Section6.LocalTest (ball 0 r) → ℝ) := fun p φ =>
    hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (a * Real.log ‖x‖)
  let T : Set ((Section6.LocalTest (ball 0 r) → ℝ) × ℂ) :=
    {q | (phaseTorusOfComplex (-q.2), q.1) ∈ E}
  have hT : MeasurableSet T := hE.preimage
    ((measurable_phaseTorusOfComplex.comp measurable_snd.neg).prodMk measurable_fst)
  have hH : Measurable H :=
    measurable_meanZeroDistributionVersion.comp (Section6.measurable_pairingProc hh)
  have hXm : Measurable X := by
    apply measurable_pi_iff.mpr
    intro φ
    exact ((measurable_translated_distribution_pairing φ.1.1).comp
      ((hH.comp measurable_snd).prodMk measurable_fst)).add_const _
  have hYm : Measurable Y := by
    apply measurable_pi_iff.mpr
    intro φ
    exact ((hh.measurable_pairing φ.1.1 (Section6.isTestFunction_of_testC φ.1.1)).comp
      measurable_snd).add_const _
  have hg : Measurable (Function.uncurry (fun (_ : ℂ) (x : ℂ) => a * Real.log ‖x‖)) :=
    (Real.measurable_log.comp measurable_snd.norm).const_mul a
  have hdom : shiftedRootReferenceLaw (volume : Measure ℂ) P X ≪
      shiftedRootReferenceLaw (volume : Measure ℂ) P Y :=
    (hh.rooted_translated_distribution_insertion_equivalence H hH
      (fun φ => hh.canonical_distribution_version_pairing φ) volume
      (fun _ x => a * Real.log ‖x‖) hg).1
  have hfib := ae_ae_negative_centerPhase_of_ae_prod P (volume : Measure ℂ)
    Measure.AbsolutelyContinuous.rfl
    (A := fun t ω => (t, fun φ : Section6.LocalTest (ball 0 r) =>
      hC ω φ.1.1 + ∫ x, φ.1.1 x * (a * Real.log ‖x‖)) ∈ E) hphase
  have hbase : ∀ᵐ q ∂shiftedRootReferenceLaw (volume : Measure ℂ) P Y, q ∈ T := by
    apply (ae_map_iff (hYm.prodMk measurable_fst).aemeasurable hT).2
    apply (Measure.ae_prod_iff_ae_ae ((hYm.prodMk measurable_fst) hT)).2
    exact hfib
  have hx : ∀ᵐ p ∂((volume : Measure ℂ).prod P), (X p, p.1) ∈ T :=
    (ae_map_iff (hXm.prodMk measurable_fst).aemeasurable hT).1 (hdom.ae_le hbase)
  have hf := (Measure.ae_prod_iff_ae_ae ((hXm.prodMk measurable_fst) hT)).1 hx
  filter_upwards [hf] with z hz
  filter_upwards [hz] with ω hω
  change (phaseTorusOfComplex (-z), X (z, ω)) ∈ E at hω
  convert hω using 1
  congr 1
  funext φ
  change H ω (LQGMetric.testAffinePull 1 z φ.1.1) +
      logInsertionDistribution z a (LQGMetric.testAffinePull 1 z φ.1.1) = _
  rw [logInsertionDistribution_translated]

/-- Haar-phase validity of the chart events gives validity of the assembled
event under the actual root-inserted field at area-almost every root. -/
theorem IsWholePlaneGFF.ae_ae_chartedLocalEvent_logInsertion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (a : ℝ) (u : ℕ → ℂ) (hu : DenseRange u)
    (E : ∀ n, Set (PhaseTorus × (Section6.LocalTest (ball 0 (bufferedChartScale n / 2)) → ℝ)))
    (hE : ∀ n, MeasurableSet (E n))
    (hphase : ∀ n, ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      (p.1, fun φ : Section6.LocalTest (ball 0 (bufferedChartScale n / 2)) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (a * Real.log ‖x‖)) ∈ E n) :
    ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 →
      ∀ᵐ ω ∂P,
        ((fun ψ : {φ : ℂ → ℝ // IsTestFunction univ φ ∧ ∫ x, φ x = 0} =>
          hC ω ψ.1 + ∫ x, ψ.1 x * (a * Real.log ‖x - z‖)), z) ∈
            chartedLocalEvent (fun z => phaseTorusOfComplex (-z)) u E := by
  have hf : ∀ n, ∀ᵐ z ∂(volume : Measure ℂ), ∀ᵐ ω ∂P,
      (phaseTorusOfComplex (-z), fun φ : Section6.LocalTest (ball 0 (bufferedChartScale n / 2)) =>
        (meanZeroDistributionVersion (Section6.pairingProc hC ω) + logInsertionDistribution z a)
          (LQGMetric.testAffinePull 1 z φ.1.1)) ∈ E n := fun n =>
    hh.ae_ae_translated_origin_phase a (bufferedChartScale n / 2) (E n) (hE n) (hphase n)
  filter_upwards [ae_all_iff.mpr hf, Measure.ae_ne (volume : Measure ℂ) 0] with z hz hz0 hzball
  obtain ⟨n, hn⟩ := exists_bufferedChart_of_mem u hu z hzball hz0
  have hzunion : z ∈ ⋃ n, bufferedChartRoots u n := mem_iUnion.mpr ⟨n, hn⟩
  obtain ⟨n, hn⟩ := exists_firstChart_of_mem (bufferedChartRoots u) z hzunion
  filter_upwards [hz n, hh.ae_chartedLocalEvent_add_of_canonical
    (fun z => phaseTorusOfComplex (-z)) u E] with ω hω heq
  have h := (heq n z hn (logInsertionDistribution z a)).2 hω
  simpa only [logInsertionDistribution_apply, TestFunction.coe_mk] using h

universe u

/-- Uniform origin frequency certificates produce one measurable marked
event whose local sections transfer to almost every root of the singular
Liouville measure. The frequency interpretation at sampled roots is separate. -/
theorem IsWholePlaneGFF.exists_charted_phaseFrequency_event
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α β : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ ν : Ω → Measure ℂ} {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    (hh : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ γ hcirc μ₀)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC₀ : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hCCγ : LQGMeasureCoordChange P γ γ hC hcirc)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ u : ℕ → ℂ, DenseRange u ∧
    ∃ c a : ℝ, 0 < c ∧ a ∈ Ioo (0 : ℝ) 1 ∧
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1,
    ∀ N : ℕ, N₀ ≤ N →
    ∃ E : ∀ n, Set (PhaseTorus ×
        (Section6.LocalTest (ball 0 (bufferedChartScale n / 2)) → ℝ)),
      (∀ n, MeasurableSet (E n)) ∧
      (∀ n, ∀ᵐ ω ∂P, ∀ t : PhaseTorus,
        ((t, fun φ : Section6.LocalTest (ball 0 (bufferedChartScale n / 2)) =>
          hC ω φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) ∈ E n ↔
        ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
          ({k : ℕ | k ∈ Icc (K + 1) (2 * K) ∧
            PhaseVeryGoodAnnulus (μ₀ ω) β (dyadicScale k) 0 N
              (a / (((401 : ℝ) ^ |-(γ * γ)|) ^ 2)) b
              C₁m C₁p C₂m C₂p c (torusPhase t) ∧
            AnnulusBallComparison (μ₀ ω) k 0 m}.ncard : ℝ))) ∧
      MeasurableSet (chartedLocalEvent (fun z => phaseTorusOfComplex (-z)) u E) ∧
      (∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 →
        ∃ R : ℝ, 0 < R ∧ R < ‖z‖ ∧ ‖z‖ + R < 1 ∧
          ∃ F : Set (ModConstTestPairings (ball z R)), MeasurableSet F ∧
            (∀ v, (v, z) ∈ chartedLocalEvent (fun z => phaseTorusOfComplex (-z)) u E ↔
              restrictGlobalPairings (ball z R) v ∈ F) ∧
            ∀ᵐ ω ∂P, (fun φ => hC ω φ.1 +
              ∫ x, φ.1 x * (-γ * Real.log ‖x - z‖)) ∈ F) ∧
      (∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ ball (0 : ℂ) 1 →
        (localModConstField α hC univ ω, z) ∈
          chartedLocalEvent (fun z => phaseTorusOfComplex (-z)) u E) := by
  have hαγ : γ < lqgQ γ := by
    have hsq : γ ^ 2 < 4 := by nlinarith
    have hdiv : γ / 2 < 2 / γ := by
      apply (lt_div_iff₀ hγ).2
      nlinarith
    unfold lqgQ
    linarith
  obtain ⟨u, hu⟩ := exists_dense_seq ℂ
  obtain ⟨c, a, hc, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p,
    N₀, hN₀, m, hm, hcert⟩ :=
    hh.exists_uniform_singular_inserted_phaseFrequency_certificate hgrowth hfull
      hγ hγ2 hαγ hβ hb hμ₀ hν hAff hCC₀ hCCγ hζ
  refine ⟨u, hu, c, a, hc, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p,
    N₀, hN₀, m, hm, ?_⟩
  intro N hN
  choose E hE heq hphase using fun n : ℕ =>
    hcert N hN (bufferedChartScale n / 2) (half_pos (bufferedChartScale_pos n))
  have hS := measurableSet_chartedLocalEvent (fun z => phaseTorusOfComplex (-z))
    (measurable_phaseTorusOfComplex.comp measurable_neg) u E hE
  have hvalid := hh.ae_ae_chartedLocalEvent_logInsertion (-γ) u hu E hE hphase
  have href : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 →
      ∃ R : ℝ, 0 < R ∧ R < ‖z‖ ∧ ‖z‖ + R < 1 ∧
        ∃ F : Set (ModConstTestPairings (ball z R)), MeasurableSet F ∧
          (∀ v, (v, z) ∈ chartedLocalEvent (fun z => phaseTorusOfComplex (-z)) u E ↔
            restrictGlobalPairings (ball z R) v ∈ F) ∧
          ∀ᵐ ω ∂P, (fun φ => hC ω φ.1 +
            ∫ x, φ.1 x * (-γ * Real.log ‖x - z‖)) ∈ F := by
    filter_upwards [hvalid, Measure.ae_ne (volume : Measure ℂ) 0] with z hz hz0 hzball
    obtain ⟨R, hR, hRz, hR1, F, hF, hlocal⟩ :=
      chartedLocalEvent_admissible_section (fun z => phaseTorusOfComplex (-z))
        u hu E hE z hzball hz0
    refine ⟨R, hR, hRz, hR1, F, hF, hlocal, ?_⟩
    filter_upwards [hz hzball] with ω hω
    exact (hlocal _).1 hω
  exact ⟨E, hE, heq, hS, href,
    hh.ae_singular_root_local_of_reference hγ hγ2 hα hμ hν
      (chartedLocalEvent (fun z => phaseTorusOfComplex (-z)) u E) hS href⟩


/-- A Haar-valid origin certificate gives the corresponding good normalized
reference observation on every positive-index root domain. -/
theorem IsWholePlaneGFF.ae_localReference_good_of_phase_certificate
    (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {ν : Ω → Measure ℂ} (hh : IsWholePlaneGFF P hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hγQ : γ < lqgQ γ)
    (hν : IsLQGMeasureOfField P γ γ hcirc ν)
    {R : ℝ} (E : Set (PhaseTorus × (Section6.LocalTest (ball 0 R) → ℝ)))
    (β : ℝ) (N₀ : ℕ) (a b C₁m C₁p C₂m C₂p C₃ m ζ : ℝ)
    (hcert : ∀ᵐ ω ∂P, ∀ t : PhaseTorus,
      ((t, fun φ : Section6.LocalTest (ball 0 R) =>
        hC ω φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) ∈ E ↔
      ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
        ({n : ℕ | n ∈ Icc (K + 1) (2 * K) ∧
          PhaseVeryGoodAnnulus (ν ω) β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase t) ∧
          AnnulusBallComparison (ν ω) n 0 m}.ncard : ℝ)))
    (hphase : ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      (p.1, fun φ : Section6.LocalTest (ball 0 R) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) ∈ E) :
    ∀ j : ℕ, 1 ≤ j → ∀ᵐ p ∂((volume.restrict (localDomain j)).prod P),
      localReferenceObservation ν j p ∈
        recentredGoodSet β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hfreq : ∀ᵐ p ∂(((volume : Measure PhaseCircle).prod volume).prod P),
      ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
        ({n : ℕ | n ∈ Icc (K + 1) (2 * K) ∧
          PhaseVeryGoodAnnulus (ν p.2) β (dyadicScale n) 0 N₀
            a b C₁m C₁p C₂m C₂p C₃ (torusPhase p.1) ∧
          AnnulusBallComparison (ν p.2) n 0 m}.ncard : ℝ) := by
    filter_upwards [hphase, Measure.quasiMeasurePreserving_snd.ae hcert] with p hp hc
    exact (hc p.1).1 hp
  have hmap := MeasureTheory.QuasiMeasurePreserving.prodMap quasiMeasurePreserving_phaseTorusOfComplex
    (MeasurePreserving.id P).quasiMeasurePreserving
  have hfreq' := hmap.ae hfreq
  have htail : ∀ᵐ p ∂((volume : Measure ℂ).prod P), ∀ᶠ K : ℕ in atTop,
      (1 - ζ) * (K : ℝ) ≤ ({n : ℕ | n ∈ Icc (K + 1) (2 * K) ∧
        PhaseVeryGoodAnnulus (ν p.2) β (dyadicScale n) 0 N₀
          a b C₁m C₁p C₂m C₂p C₃ p.1 ∧
        AnnulusBallComparison (ν p.2) n 0 m}.ncard : ℝ) := by
    filter_upwards [hfreq'] with p hp
    dsimp only [Prod.map, id] at hp
    filter_upwards [hp] with K hK
    convert hK using 1
    congr 2
    ext n
    simp only [mem_ofPred_eq, phaseVeryGoodAnnulus_torusPhase_ofComplex]
  have hpos : ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → 0 < ν ω (ball 0 r) := by
    filter_upwards [hfull γ γ hγ hγ2 hγQ Ω P hC hcirc ν hh hν] with ω hω r hr
    exact hω _ isOpen_ball (nonempty_ball.mpr hr)
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (ν ω) :=
    hν.mono fun _ h => h.isLocallyFiniteMeasure
  intro j hj
  exact localReference_ae_mem_of_tail P ν β N₀ a b C₁m C₁p C₂m C₂p C₃ m ζ
    htail hpos hloc j hj


/-- Uniform phase-frequency estimates give good normalized reference
observations on every local root domain. -/
theorem IsWholePlaneGFF.exists_uniform_good_localReference
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ β : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ₀ ν : Ω → Measure ℂ} {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    (hh : IsWholePlaneGFF P hC hcirc)
    (hμ₀ : IsLQGMeasureOfField P γ γ hcirc μ₀)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC₀ : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hCCγ : LQGMeasureCoordChange P γ γ hC hcirc)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ c a : ℝ, 0 < c ∧ a ∈ Ioo (0 : ℝ) 1 ∧
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1,
    ∀ N : ℕ, N₀ ≤ N → ∀ j : ℕ, 1 ≤ j →
      ∀ᵐ p ∂((volume.restrict (localDomain j)).prod P),
        localReferenceObservation μ₀ j p ∈ recentredGoodSet β N
          (a / (((401 : ℝ) ^ |-(γ * γ)|) ^ 2)) b
          C₁m C₁p C₂m C₂p c m ζ := by
  have hγQ : γ < lqgQ γ := by
    have hsq : γ ^ 2 < 4 := by nlinarith
    have hdiv : γ / 2 < 2 / γ := by
      apply (lt_div_iff₀ hγ).2
      nlinarith
    unfold lqgQ
    linarith
  obtain ⟨c, a, hc, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p,
    N₀, hN₀, m, hm, hcert⟩ :=
    hh.exists_uniform_singular_inserted_phaseFrequency_certificate hgrowth hfull
      hγ hγ2 hγQ hβ hb hμ₀ hν hAff hCC₀ hCCγ hζ
  refine ⟨c, a, hc, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p,
    N₀, hN₀, m, hm, ?_⟩
  intro N hN
  obtain ⟨E, _, heq, hphase⟩ := hcert N hN 1 zero_lt_one
  exact hh.ae_localReference_good_of_phase_certificate hfull hγ hγ2 hγQ hμ₀ E
    β N _ b C₁m C₁p C₂m C₂p c m ζ heq hphase


/-- The charted marked event and the normalized reference observations
share the same frequency parameters at every admissible index. -/
theorem IsWholePlaneGFF.exists_charted_phaseFrequency_event_with_reference
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α β : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ ν : Ω → Measure ℂ} {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    (hh : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ γ hcirc μ₀)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC₀ : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hCCγ : LQGMeasureCoordChange P γ γ hC hcirc)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ u : ℕ → ℂ, DenseRange u ∧
    ∃ c a : ℝ, 0 < c ∧ a ∈ Ioo (0 : ℝ) 1 ∧
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1,
    ∀ N : ℕ, N₀ ≤ N →
    ∃ E : ∀ n, Set (PhaseTorus ×
        (Section6.LocalTest (ball 0 (bufferedChartScale n / 2)) → ℝ)),
      (∀ n, MeasurableSet (E n)) ∧
      (∀ n, ∀ᵐ ω ∂P, ∀ t : PhaseTorus,
        ((t, fun φ : Section6.LocalTest (ball 0 (bufferedChartScale n / 2)) =>
          hC ω φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) ∈ E n ↔
        ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
          ({k : ℕ | k ∈ Icc (K + 1) (2 * K) ∧
            PhaseVeryGoodAnnulus (μ₀ ω) β (dyadicScale k) 0 N
              (a / (((401 : ℝ) ^ |-(γ * γ)|) ^ 2)) b
              C₁m C₁p C₂m C₂p c (torusPhase t) ∧
            AnnulusBallComparison (μ₀ ω) k 0 m}.ncard : ℝ))) ∧
      MeasurableSet (chartedLocalEvent (fun z => phaseTorusOfComplex (-z)) u E) ∧
      (∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 →
        ∃ R : ℝ, 0 < R ∧ R < ‖z‖ ∧ ‖z‖ + R < 1 ∧
          ∃ F : Set (ModConstTestPairings (ball z R)), MeasurableSet F ∧
            (∀ v, (v, z) ∈ chartedLocalEvent (fun z => phaseTorusOfComplex (-z)) u E ↔
              restrictGlobalPairings (ball z R) v ∈ F) ∧
            ∀ᵐ ω ∂P, (fun φ => hC ω φ.1 +
              ∫ x, φ.1 x * (-γ * Real.log ‖x - z‖)) ∈ F) ∧
      (∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ ball (0 : ℂ) 1 →
        (localModConstField α hC univ ω, z) ∈
          chartedLocalEvent (fun z => phaseTorusOfComplex (-z)) u E) ∧
      (∀ j : ℕ, 1 ≤ j → ∀ᵐ p ∂((volume.restrict (localDomain j)).prod P),
        localReferenceObservation μ₀ j p ∈ recentredGoodSet β N
          (a / (((401 : ℝ) ^ |-(γ * γ)|) ^ 2)) b
          C₁m C₁p C₂m C₂p c m ζ) := by
  have hαγ : γ < lqgQ γ := by
    have hsq : γ ^ 2 < 4 := by nlinarith
    have hdiv : γ / 2 < 2 / γ := by
      apply (lt_div_iff₀ hγ).2
      nlinarith
    unfold lqgQ
    linarith
  obtain ⟨u, hu⟩ := exists_dense_seq ℂ
  obtain ⟨c, a, hc, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p,
    N₀, hN₀, m, hm, hcert⟩ :=
    hh.exists_uniform_singular_inserted_phaseFrequency_certificate hgrowth hfull
      hγ hγ2 hαγ hβ hb hμ₀ hν hAff hCC₀ hCCγ hζ
  refine ⟨u, hu, c, a, hc, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p,
    N₀, hN₀, m, hm, ?_⟩
  intro N hN
  choose E hE heq hphase using fun n : ℕ =>
    hcert N hN (bufferedChartScale n / 2) (half_pos (bufferedChartScale_pos n))
  have hS := measurableSet_chartedLocalEvent (fun z => phaseTorusOfComplex (-z))
    (measurable_phaseTorusOfComplex.comp measurable_neg) u E hE
  have hvalid := hh.ae_ae_chartedLocalEvent_logInsertion (-γ) u hu E hE hphase
  have href : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 →
      ∃ R : ℝ, 0 < R ∧ R < ‖z‖ ∧ ‖z‖ + R < 1 ∧
        ∃ F : Set (ModConstTestPairings (ball z R)), MeasurableSet F ∧
          (∀ v, (v, z) ∈ chartedLocalEvent (fun z => phaseTorusOfComplex (-z)) u E ↔
            restrictGlobalPairings (ball z R) v ∈ F) ∧
          ∀ᵐ ω ∂P, (fun φ => hC ω φ.1 +
            ∫ x, φ.1 x * (-γ * Real.log ‖x - z‖)) ∈ F := by
    filter_upwards [hvalid, Measure.ae_ne (volume : Measure ℂ) 0] with z hz hz0 hzball
    obtain ⟨R, hR, hRz, hR1, F, hF, hlocal⟩ :=
      chartedLocalEvent_admissible_section (fun z => phaseTorusOfComplex (-z))
        u hu E hE z hzball hz0
    refine ⟨R, hR, hRz, hR1, F, hF, hlocal, ?_⟩
    filter_upwards [hz hzball] with ω hω
    exact (hlocal _).1 hω
  exact ⟨E, hE, heq, hS, href,
    hh.ae_singular_root_local_of_reference hγ hγ2 hα hμ hν
      (chartedLocalEvent (fun z => phaseTorusOfComplex (-z)) u E) hS href,
    hh.ae_localReference_good_of_phase_certificate hfull hγ hγ2 hαγ hμ₀ (E 0)
      β N _ b C₁m C₁p C₂m C₂p c m ζ (heq 0) (hphase 0)⟩


/-- The charted event and a jointly measurable actual-frequency event use the same parameters. -/
theorem IsWholePlaneGFF.exists_charted_phaseFrequency_event_with_joint_frequency
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u}) (hfull : LQGMeasureFullSupportStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α β : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α < lqgQ γ)
    (hβ : (2 + γ) ^ 2 / 2 < β)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ μ₀ ν : Ω → Measure ℂ} {b : ℝ} (hb : b ∈ Ioo (0 : ℝ) 1)
    (hh : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α hcirc μ)
    (hμ₀ : IsLQGMeasureOfField P γ γ hcirc μ₀)
    (hν : IsLQGMeasureOfField P γ 0 hcirc ν)
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC₀ : LQGMeasureCoordChange P γ 0 hC hcirc)
    (hCCγ : LQGMeasureCoordChange P γ γ hC hcirc)
    {ζ : ℝ} (hζ : 0 < ζ) :
    ∃ u : ℕ → ℂ, DenseRange u ∧
    ∃ c a : ℝ, 0 < c ∧ a ∈ Ioo (0 : ℝ) 1 ∧
    ∃ C₁m C₁p C₂m C₂p : ℝ,
      0 < C₁m ∧ 0 < C₁p ∧ 0 < C₂m ∧ 0 < C₂p ∧
    ∃ N₀ : ℕ, 9 ≤ N₀ ∧ ∃ m ∈ Ioo (0 : ℝ) 1,
    ∀ N : ℕ, N₀ ≤ N →
    ∃ E : ∀ n, Set (PhaseTorus ×
        (Section6.LocalTest (ball 0 (bufferedChartScale n / 2)) → ℝ)),
      (∀ n, MeasurableSet (E n)) ∧
      (∀ n, ∀ᵐ ω ∂P, ∀ t : PhaseTorus,
        ((t, fun φ : Section6.LocalTest (ball 0 (bufferedChartScale n / 2)) =>
          hC ω φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) ∈ E n ↔
        ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
          ({k : ℕ | k ∈ Icc (K + 1) (2 * K) ∧
            PhaseVeryGoodAnnulus (μ₀ ω) β (dyadicScale k) 0 N
              (a / (((401 : ℝ) ^ |-(γ * γ)|) ^ 2)) b
              C₁m C₁p C₂m C₂p c (torusPhase t) ∧
            AnnulusBallComparison (μ₀ ω) k 0 m}.ncard : ℝ))) ∧
      MeasurableSet (chartedLocalEvent (fun z => phaseTorusOfComplex (-z)) u E) ∧
      (∀ᵐ z ∂(volume : Measure ℂ), z ∈ ball (0 : ℂ) 1 →
        ∃ R : ℝ, 0 < R ∧ R < ‖z‖ ∧ ‖z‖ + R < 1 ∧
          ∃ F : Set (ModConstTestPairings (ball z R)), MeasurableSet F ∧
            (∀ v, (v, z) ∈ chartedLocalEvent (fun z => phaseTorusOfComplex (-z)) u E ↔
              restrictGlobalPairings (ball z R) v ∈ F) ∧
            ∀ᵐ ω ∂P, (fun φ => hC ω φ.1 +
              ∫ x, φ.1 x * (-γ * Real.log ‖x - z‖)) ∈ F) ∧
      (∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ ball (0 : ℂ) 1 →
        (localModConstField α hC univ ω, z) ∈
          chartedLocalEvent (fun z => phaseTorusOfComplex (-z)) u E) ∧
      (∀ j : ℕ, 1 ≤ j → ∀ᵐ p ∂((volume.restrict (localDomain j)).prod P),
        localReferenceObservation μ₀ j p ∈ recentredGoodSet β N
          (a / (((401 : ℝ) ^ |-(γ * γ)|) ^ 2)) b
          C₁m C₁p C₂m C₂p c m ζ) ∧
      ∃ F : Set (Ω × ℂ), MeasurableSet F ∧ ∀ᵐ ω ∂P, ∀ z : ℂ,
        (ω, z) ∈ F ↔ ∀ᶠ K : ℕ in atTop, (1 - ζ) * (K : ℝ) ≤
          (veryGoodComparableScaleCount (μ ω) β z N
            (a / (((401 : ℝ) ^ |-(γ * γ)|) ^ 2)) b
            C₁m C₁p C₂m C₂p c m K : ℝ) := by
  obtain ⟨u, hu, c, a, hc, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p,
    N₀, hN₀, m, hm, hcert⟩ :=
    hh.exists_charted_phaseFrequency_event_with_reference hgrowth hfull hγ hγ2 hα hβ hb
      hμ hμ₀ hν hAff hCC₀ hCCγ hζ
  refine ⟨u, hu, c, a, hc, ha, C₁m, C₁p, C₂m, C₂p, h₁m, h₁p, h₂m, h₂p,
    N₀, hN₀, m, hm, ?_⟩
  intro N hN
  obtain ⟨E, hE, heq, hS, href, hroot, hlocal⟩ := hcert N hN
  refine ⟨E, hE, heq, hS, href, hroot, hlocal, ?_⟩
  have hapos : 0 < a / (((401 : ℝ) ^ |-(γ * γ)|) ^ 2) := by
    have := ha.1
    positivity
  exact exists_jointlyMeasurable_veryGoodComparableScaleFrequency P
    (hh.aemeasurable_lqgMeasure hμ) (hμ.mono fun _ h => h.isLocallyFiniteMeasure)
    β N _ b C₁m C₁p C₂m C₂p c m ζ (measurableSet_unitGoodAnnulus _ b hapos)

end HarmonicBalls
