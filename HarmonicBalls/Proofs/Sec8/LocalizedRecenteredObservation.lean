import HarmonicBalls.Proofs.Sec8.RecenteredRootedObservation

/-! # Localizing recentered rooted observations

A comparison of rooted laws remains valid when both laws are restricted to a
measurable set of roots. This permits a buffered local comparison to be applied
on subsets without assuming a separate rooted-law comparison for each subset.
The imported Section 6 development uses Leonardo Bonanno's whole-plane GFF
formalization.
-/

namespace HarmonicBalls

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal

/-- Restricting a shifted reference law by its root coordinate restricts the
independent root measure. -/
theorem shiftedRootReferenceLaw_restrict_root
    {Z Ω F : Type*} [MeasurableSpace Z] [MeasurableSpace Ω] [MeasurableSpace F]
    (ρ : Measure Z) (P : Measure Ω) [SFinite ρ] [SFinite P] (X : Z × Ω → F) (hX : Measurable X)
    (B : Set Z) (hB : MeasurableSet B) :
    (shiftedRootReferenceLaw ρ P X).restrict {q | q.2 ∈ B} =
      shiftedRootReferenceLaw (ρ.restrict B) P X := by
  unfold shiftedRootReferenceLaw
  change ((ρ.prod P).map (fun x => (X x, x.1))).restrict (Prod.snd ⁻¹' B) = _
  rw [Measure.restrict_map (hX.prodMk measurable_fst) (measurable_snd hB),
    Measure.restrict_prod_eq_prod_univ]
  have hset : (fun x : Z × Ω => (X x, x.1)) ⁻¹' (Prod.snd ⁻¹' B) = B ×ˢ univ := by
    ext x
    simp
  rw [hset]

/-- A rooted-law comparison may be restricted to a measurable set of roots
before applying the buffered local comparison. -/
theorem IsWholePlaneGFF.localized_recentered_observation_ac_origin_insertion
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (ρ : Measure ℂ) [SFinite ρ] (γ : ℝ)
    (B : Set ℂ) (hB : MeasurableSet B)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hside : ∀ᵐ z ∂(ρ.restrict B), ‖z‖ + R ≤ 1 ∨ 1 + R ≤ ‖z‖)
    (M : Measure ((LQGMetric.TestC0 → ℝ) × ℂ))
    (hrooted : M ≪ shiftedRootReferenceLaw ρ P (fun p =>
      fun φ : LQGMetric.TestC0 => hC p.2 φ.1 + ∫ x, φ.1 x *
        (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1)))) :
    (M.restrict {q | q.2 ∈ B}).map
      (fun q => (recenteredDistributionObservation (ball 0 r) q, q.2)) ≪
      shiftedRootReferenceLaw (ρ.restrict B) P (fun p =>
        fun φ : Section6.LocalTest (ball 0 r) =>
          hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖)) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  apply hh.recentered_observation_ac_origin_insertion (ρ.restrict B) γ hr hrR hside
  have h := hrooted.restrict {q | q.2 ∈ B}
  rw [shiftedRootReferenceLaw_restrict_root ρ P _
    (hh.measurable_wholePlane_inserted_pairings γ) B hB] at h
  exact h


/-- One global rooted comparison yields local reference properties at almost
all roots in any measurable buffered subset of the sampling set. -/
theorem IsWholePlaneGFF.ae_ae_localized_recentered_observation
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (μ : Ω → Measure ℂ)
    (hμ : AEMeasurable μ P) (A B : Set ℂ) (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hfin : ∀ᵐ ω ∂P, μ ω A ≠ ∞)
    (ρ : Measure ℂ) [SFinite ρ] (γ : ℝ)
    {r R : ℝ} (hr : 0 < r) (hrR : r < R)
    (hside : ∀ᵐ z ∂(ρ.restrict B), ‖z‖ + R ≤ 1 ∨ 1 + R ≤ ‖z‖)
    (hrooted : (P.bind fun ω => ((μ ω).restrict A).map
      (fun z => (Section6.pairingProc hC ω, z))) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
        hC p.2 φ.1 + ∫ x, φ.1 x *
          (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1))))
    (E : Set ((Section6.LocalTest (ball 0 r) → ℝ) × ℂ)) (hE : MeasurableSet E)
    (href : ∀ᵐ q ∂(shiftedRootReferenceLaw (ρ.restrict B) P (fun p =>
      fun φ : Section6.LocalTest (ball 0 r) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖))), q ∈ E) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ A → z ∈ B →
      (recenteredDistributionObservation (ball 0 r) (Section6.pairingProc hC ω, z), z) ∈ E := by
  let M := P.bind fun ω => ((μ ω).restrict A).map
    (fun z => (Section6.pairingProc hC ω, z))
  let T := fun q => (recenteredDistributionObservation (ball 0 r) q, q.2)
  have hT : Measurable T :=
    (measurable_recenteredDistributionObservation (ball 0 r)).prodMk measurable_snd
  have hdom := hh.localized_recentered_observation_ac_origin_insertion ρ γ B hB
    hr hrR hside M hrooted
  have hrestricted : ∀ᵐ q ∂(M.restrict {q | q.2 ∈ B}), T q ∈ E :=
    (ae_map_iff hT.aemeasurable hE).1 (hdom.ae_le href)
  have hall : ∀ᵐ q ∂M, q.2 ∈ B → T q ∈ E :=
    (ae_restrict_iff' (measurable_snd hB)).1 hrestricted
  exact ae_ae_mem_of_observed_restricted_bind P μ hμ (Section6.pairingProc hC)
    (Section6.measurable_pairingProc hh) A hA hfin hall


/-- A single rooted-law comparison supplies local reference properties on
all sets in a countable family, allowing the observation radius to vary. -/
theorem IsWholePlaneGFF.ae_ae_countable_localized_recentered_observations
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (μ : Ω → Measure ℂ)
    (hμ : AEMeasurable μ P) (A : Set ℂ) (hA : MeasurableSet A)
    (hfin : ∀ᵐ ω ∂P, μ ω A ≠ ∞) (ρ : Measure ℂ) [SFinite ρ] (γ : ℝ)
    (B : ℕ → Set ℂ) (hB : ∀ n, MeasurableSet (B n))
    (r R : ℕ → ℝ) (hr : ∀ n, 0 < r n) (hrR : ∀ n, r n < R n)
    (hside : ∀ n, ∀ᵐ z ∂(ρ.restrict (B n)),
      ‖z‖ + R n ≤ 1 ∨ 1 + R n ≤ ‖z‖)
    (hrooted : (P.bind fun ω => ((μ ω).restrict A).map
      (fun z => (Section6.pairingProc hC ω, z))) ≪
      shiftedRootReferenceLaw ρ P (fun p => fun φ : LQGMetric.TestC0 =>
        hC p.2 φ.1 + ∫ x, φ.1 x *
          (-γ * Real.log ‖x - p.1‖ + γ * Real.log (max ‖x‖ 1))))
    (E : ∀ n, Set ((Section6.LocalTest (ball 0 (r n)) → ℝ) × ℂ))
    (hE : ∀ n, MeasurableSet (E n))
    (href : ∀ n, ∀ᵐ q ∂(shiftedRootReferenceLaw (ρ.restrict (B n)) P (fun p =>
      fun φ : Section6.LocalTest (ball 0 (r n)) =>
        hC p.2 φ.1.1 + ∫ x, φ.1.1 x * (-γ * Real.log ‖x‖))), q ∈ E n) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ A → ∀ n, z ∈ B n →
      (recenteredDistributionObservation (ball 0 (r n)) (Section6.pairingProc hC ω, z), z) ∈ E n := by
  have h : ∀ n, ∀ᵐ ω ∂P, ∀ᵐ z ∂μ ω, z ∈ A → z ∈ B n →
      (recenteredDistributionObservation (ball 0 (r n)) (Section6.pairingProc hC ω, z), z) ∈ E n :=
    fun n => hh.ae_ae_localized_recentered_observation μ hμ A (B n) hA (hB n)
      hfin ρ γ (hr n) (hrR n) (hside n) hrooted (E n) (hE n) (href n)
  filter_upwards [ae_all_iff.mpr h] with ω hω
  filter_upwards [ae_all_iff.mpr hω] with z hz hza n hzb
  exact hz n hza hzb


/-- The roots at distance greater than `1 / (n + 1)` from the unit circle,
on its interior side. -/
def unitBallBufferedRoots (n : ℕ) : Set ℂ :=
  {z | ‖z‖ + 1 / ((n : ℝ) + 1) < 1}

/-- Each buffered root set is measurable. -/
theorem measurableSet_unitBallBufferedRoots (n : ℕ) :
    MeasurableSet (unitBallBufferedRoots n) := by
  exact (measurable_norm.add measurable_const) measurableSet_Iio

/-- The buffered root sets cover the open unit disk. -/
theorem unitBallBufferedRoots_cover {z : ℂ} (hz : z ∈ ball 0 1) :
    ∃ n, z ∈ unitBallBufferedRoots n := by
  have hz' : ‖z‖ < 1 := by simpa [mem_ball, dist_eq_norm] using hz
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr hz')
  refine ⟨n, ?_⟩
  change ‖z‖ + 1 / ((n : ℝ) + 1) < 1
  linarith

/-- On a buffered root set the corresponding translated ball stays inside
the unit circle. -/
theorem ae_unitBallBufferedRoots_side (ρ : Measure ℂ) (n : ℕ) :
    ∀ᵐ z ∂(ρ.restrict (unitBallBufferedRoots n)),
      ‖z‖ + 1 / ((n : ℝ) + 1) ≤ 1 ∨
        1 + 1 / ((n : ℝ) + 1) ≤ ‖z‖ := by
  filter_upwards [ae_restrict_mem (measurableSet_unitBallBufferedRoots n)] with z hz
  exact Or.inl (le_of_lt hz)

end HarmonicBalls
