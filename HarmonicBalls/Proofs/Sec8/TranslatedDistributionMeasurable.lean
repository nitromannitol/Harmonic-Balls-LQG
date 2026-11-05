import HarmonicBalls.Proofs.Sec8.MeanZeroDistributionVersion
import LatticeProb.Bonanno.LQGMetric.Field.MeasurableAvg

/-! # Measurability of translated distribution pairings

The test-family continuity argument adapts Leonardo Bonanno's proof of
`continuous_bumpTest` in LatticeProb. -/

noncomputable section

open MeasureTheory Filter Topology Set TopologicalSpace Metric
open scoped Distributions

namespace HarmonicBalls

/-- Translation is continuous in the test-function topology. -/
theorem continuous_testAffinePull_one (φ : LQGMetric.TestC) :
    Continuous (fun z : ℂ => LQGMetric.testAffinePull 1 z φ) := by
  obtain ⟨R, hR⟩ := φ.hasCompactSupport.isBounded.subset_closedBall 0
  rw [continuous_iff_continuousAt]
  intro z₀
  let S := closedBall z₀ 1
  have : CompactSpace S := isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)
  let K : Compacts ℂ := ⟨closedBall 0 (‖z₀‖ + 1 + R), isCompact_closedBall _ _⟩
  have hs : ∀ z : S, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun y => φ (y + -(z : ℂ))) :=
    fun z => φ.contDiff.comp (contDiff_id.add contDiff_const)
  have hK : ∀ z : S, ∀ y ∉ (K : Set ℂ), φ (y + -(z : ℂ)) = 0 := by
    intro z y hy
    by_contra hn
    have hm : y + -(z : ℂ) ∈ tsupport (φ : ℂ → ℝ) :=
      subset_closure hn
    have hb : ‖y + -(z : ℂ)‖ ≤ R := by
      simpa only [mem_closedBall, dist_zero_right] using hR hm
    have hz : ‖(z : ℂ) - z₀‖ ≤ 1 := by rw [← dist_eq_norm]; exact mem_closedBall.1 z.2
    have hy' : ‖z₀‖ + 1 + R < ‖y‖ := by simpa [K] using hy
    have ht : ‖y‖ ≤ ‖y + -(z : ℂ)‖ + ‖(z : ℂ) - z₀‖ + ‖z₀‖ := by
      calc ‖y‖ = ‖(y + -(z : ℂ)) + ((z : ℂ) - z₀) + z₀‖ := by ring_nf
        _ ≤ _ := norm_add₃_le
    linarith
  have hD : ∀ i : ℕ, Continuous fun p : S × ℂ =>
      iteratedFDeriv ℝ i (fun y => φ (y + -(p.1 : ℂ))) p.2 := by
    intro i
    simp_rw [iteratedFDeriv_comp_add_right]
    exact (φ.contDiff.continuous_iteratedFDeriv (by exact_mod_cast le_top)).comp
      (continuous_snd.add (continuous_subtype_val.comp continuous_fst).neg)
  have hc := LQGMetric.continuous_testFamK K (fun (z : S) y => φ (y + -(z : ℂ))) hs hK hD
  have he : (fun z : S => LQGMetric.testAffinePull 1 z φ) =
      LQGMetric.ofSuppC K ∘ LQGMetric.testFamK K _ hs hK := by
    funext z
    ext y
    simp [LQGMetric.testAffinePull_apply, LQGMetric.ofSuppC, LQGMetric.testFamK, sub_eq_add_neg]
    rfl
  have h2 : Continuous fun z : S => LQGMetric.testAffinePull 1 z φ := by
    rw [he]
    exact (LQGMetric.ofSuppC K).continuous.comp hc
  exact (continuousOn_iff_continuous_domRestrict.2 h2).continuousAt
    (closedBall_mem_nhds _ one_pos)

/-- Distribution evaluation against translated tests is jointly measurable. -/
theorem measurable_translated_distribution_pairing (φ : LQGMetric.TestC) :
    Measurable (fun p : LQGMetric.DistC × ℂ =>
      p.1 (LQGMetric.testAffinePull 1 p.2 φ)) := by
  have h := measurable_uncurry_of_continuous_of_measurable
    (u := fun (z : ℂ) (H : LQGMetric.DistC) => H (LQGMetric.testAffinePull 1 z φ))
    (fun H => (map_continuous H).comp (continuous_testAffinePull_one φ))
    (fun z => LQGMetric.measurable_distOn_apply _)
  exact h.comp measurable_swap

/-- A measurable distribution-valued field has jointly measurable translated
mean-zero pairings. -/
theorem measurable_translated_distribution_pairProc
    {Ω : Type*} [MeasurableSpace Ω] {H : Ω → LQGMetric.DistC} (hH : Measurable H) :
    Measurable (fun p : ℂ × Ω => fun φ : LQGMetric.TestC0 =>
      H p.2 (LQGMetric.testAffinePull 1 p.1 φ.1)) := by
  apply measurable_pi_iff.mpr
  intro φ
  exact (measurable_translated_distribution_pairing φ.1).comp
    ((hH.comp measurable_snd).prodMk measurable_fst)

/-- Coordinatewise almost-sure equality suffices for equality of full
cylinder laws, even when the exceptional set depends on the coordinate. -/
theorem map_pi_eq_of_coordinatewise_ae_eq
    {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {F G : Ω → ι → ℝ} (hF : Measurable F) (hG : Measurable G)
    (h : ∀ i, (fun ω => F ω i) =ᵐ[P] (fun ω => G ω i)) :
    P.map F = P.map G := by
  apply IsProjectiveLimit.unique (P := fun I => (P.map G).map I.restrict)
  · intro I
    dsimp only
    rw [Measure.map_map (Finset.measurable_restrict I) hF,
      Measure.map_map (Finset.measurable_restrict I) hG]
    apply Measure.map_congr
    filter_upwards [ae_all_iff.mpr (fun i : I => h i)] with ω hω
    funext i
    exact hω i
  · intro I
    rfl

/-- Every fixed translate of a distribution version has the original full
mean-zero pairing law. -/
theorem IsWholePlaneGFF.map_translated_distribution_version_eq
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (H : Ω → LQGMetric.DistC)
    (hH : Measurable H)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1)) (z : ℂ) :
    P.map (fun ω (φ : LQGMetric.TestC0) =>
      H ω (LQGMetric.testAffinePull 1 z φ.1)) =
    P.map (Section6.pairingProc hC) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hmeas : Measurable (fun ω (φ : LQGMetric.TestC0) =>
      hC ω (LQGMetric.testAffinePull 1 z φ.1)) := by
    apply measurable_pi_iff.mpr
    intro φ
    exact (measurable_pi_apply (LQGMetric.GFFInv.pull0 1 z (by norm_num) φ)).comp
      (Section6.measurable_pairingProc hh)
  calc
    _ = P.map (fun ω (φ : LQGMetric.TestC0) =>
        hC ω (LQGMetric.testAffinePull 1 z φ.1)) := by
      apply map_pi_eq_of_coordinatewise_ae_eq
      · exact (measurable_translated_distribution_pairProc hH).comp measurable_prodMk_left
      · exact hmeas
      · intro φ
        exact hversion (LQGMetric.GFFInv.pull0 1 z (by norm_num) φ)
    _ = _ := hh.map_translated_pairingProc_eq z

/-- Translation of a measurable distribution version and the original
mean-zero field have equivalent joint laws with an independent root retained. -/
theorem IsWholePlaneGFF.rooted_translated_distribution_version_equivalence
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (H : Ω → LQGMetric.DistC)
    (hH : Measurable H)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1)) (ρ : Measure ℂ) :
    let A := shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
      H p.2 (LQGMetric.testAffinePull 1 p.1 φ.1))
    let B := shiftedRootReferenceLaw ρ P (fun p => Section6.pairingProc hC p.2)
    A ≪ B ∧ B ≪ A := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  have hjoint := measurable_translated_distribution_pairProc hH
  have hbase : Measurable (fun p : ℂ × Ω => Section6.pairingProc hC p.2) :=
    (Section6.measurable_pairingProc hh).comp measurable_snd
  constructor
  · apply shiftedRootReferenceLaw_absolutelyContinuous_of_fiberwise ρ P P _ _ hjoint hbase
    exact Filter.Eventually.of_forall (fun z => Measure.absolutelyContinuous_of_le
      (hh.map_translated_distribution_version_eq H hH hversion z).le)
  · apply shiftedRootReferenceLaw_absolutelyContinuous_of_fiberwise ρ P P _ _ hbase hjoint
    exact Filter.Eventually.of_forall (fun z => Measure.absolutelyContinuous_of_le
      (hh.map_translated_distribution_version_eq H hH hversion z).symm.le)

/-- A frozen whole-plane GFF admits a distribution version whose translated
root-field law is equivalent to its independent-root pairing law. Agreement
with the original field is for each deterministic test separately. -/
theorem IsWholePlaneGFF.exists_rooted_translated_distribution_version
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (ρ : Measure ℂ) :
    ∃ H : Ω → LQGMetric.DistC, Measurable H ∧
      (∀ φ : LQGMetric.TestC0,
        (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1)) ∧
      let A := shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
        H p.2 (LQGMetric.testAffinePull 1 p.1 φ.1))
      let B := shiftedRootReferenceLaw ρ P (fun p => Section6.pairingProc hC p.2)
      A ≪ B ∧ B ≪ A := by
  obtain ⟨H, hH, hversion⟩ := hh.exists_meanZero_distribution_version
  exact ⟨H, hH, hversion, hh.rooted_translated_distribution_version_equivalence H hH hversion ρ⟩

#print axioms continuous_testAffinePull_one
#print axioms measurable_translated_distribution_pairing
#print axioms IsWholePlaneGFF.exists_rooted_translated_distribution_version

end HarmonicBalls
