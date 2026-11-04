import HarmonicBalls.Proofs.Sec5.LocalClusterFamily
import HarmonicBalls.Proofs.Sec3.Basic
import HarmonicBalls.Proofs.Sec5.ThresholdContinuity

/-! # Local compact-containment family for disc clusters -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped ENNReal Topology

universe u

/-- The compact-containment predicates of the entire positive-time disc
cluster family have a field-local representative. Equality holds at all
centres and times on one event of full probability. The field locality input
is proposed and awaits source review. -/
theorem exists_local_lqg_compactContainmentFamily_representative
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) {R : ℝ} (hR : 0 < R) :
    ∃ F : Ω → (ball (0 : ℂ) R × Ioi (0 : ℝ) → Prop),
      Measurable[fieldSigmaAlgebra α₀ hC (ball 0 R)] F ∧
      ∀ᵐ ω ∂P, ∀ p, F ω p ↔ closure (cluster (μ ω) R p.1 p.2) ⊆ ball 0 R := by
  classical
  obtain ⟨G, hG, heq⟩ := exists_local_lqg_clusterFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hR
  let J := ball (0 : ℂ) R × Ioi (0 : ℝ)
  let F : Ω → J → Prop := fun ω p => ∃ n : ℕ, ∀ m : ℕ,
    denseSeq ℂ m ∈ G ω p → denseSeq ℂ m ∈ closedBall 0 (R - 1 / ((n : ℝ) + 1))
  have hF : Measurable[fieldSigmaAlgebra α₀ hC (ball 0 R)] F := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC (ball 0 R)
    apply Measurable.of_eval
    intro p
    apply Measurable.exists
    intro n
    apply Measurable.forall
    intro m
    have hm : Measurable (fun ω => denseSeq ℂ m ∈ G ω p) :=
      (measurable_pi_apply (denseSeq ℂ m)).comp ((measurable_pi_apply p).comp hG)
    exact hm.imp measurable_const
  refine ⟨F, hF, ?_⟩
  filter_upwards [heq, clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα
    Ω P hC hcirc μ hGFF hμ] with ω hEq hOpen
  intro p
  have hop := (hOpen p.2 R p.2.property hR p.1 p.1.property).1
  have hcl : closure (cluster (μ ω) R p.1 p.2) ⊆ closedBall (0 : ℂ) R :=
    closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall
  have hk : IsCompact (closure (cluster (μ ω) R p.1 p.2)) :=
    (isCompact_closedBall (0 : ℂ) R).of_isClosed_subset isClosed_closure hcl
  rw [compact_subset_ball_iff_closedBall_exhaustion hk]
  simp only [F, hEq, closure_subset_closedBall_iff_denseSeq hop]

/-- The exact compact-containment horizon for each centre has a field-local
representative. The characterization holds simultaneously for all centres and
positive times, and does not presuppose continuity at boundary contact. -/
theorem exists_fieldLocal_centre_containment_horizons
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) {R : ℝ} (hR : 0 < R) :
    ∃ H : Ω → (ball (0 : ℂ) R → ℝ≥0∞),
      Measurable[fieldSigmaAlgebra α₀ hC (ball 0 R)] H ∧
      ∀ᵐ ω ∂P, ∀ z : ball (0 : ℂ) R, ∀ t : ℝ, 0 < t →
        (ENNReal.ofReal t < H ω z ↔ ∃ s : ℝ, t < s ∧
          closure (cluster (μ ω) R z s) ⊆ ball 0 R) := by
  classical
  obtain ⟨F, hF, heq⟩ := exists_local_lqg_compactContainmentFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hR
  let Q := {q : ℚ // 0 < (q : ℝ)}
  let H : Ω → (ball (0 : ℂ) R → ℝ≥0∞) := fun ω z => ⨆ q : Q,
    if F ω (z, ⟨q, q.property⟩) then ENNReal.ofReal q else 0
  have hH : Measurable[fieldSigmaAlgebra α₀ hC (ball 0 R)] H := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC (ball 0 R)
    apply Measurable.of_eval
    intro z
    apply Measurable.iSup
    intro q
    apply Measurable.ite _ measurable_const measurable_const
    have hm : Measurable (fun ω => F ω (z, ⟨(q : ℚ), q.property⟩)) :=
      (measurable_pi_apply (z, (⟨(q : ℚ), q.property⟩ : Ioi (0 : ℝ)))).comp hF
    exact hm.setOf
  refine ⟨H, hH, ?_⟩
  filter_upwards [heq, clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα
    Ω P hC hcirc μ hGFF hμ] with ω heqω hmono
  intro z t ht
  constructor
  · intro hlt
    change ENNReal.ofReal t < ⨆ q : Q,
      if F ω (z, ⟨q, q.property⟩) then ENNReal.ofReal q else 0 at hlt
    obtain ⟨q, hq⟩ := lt_iSup_iff.mp hlt
    by_cases hgood : F ω (z, ⟨q, q.property⟩)
    · rw [ite_eq_left hgood] at hq
      exact ⟨q, (ENNReal.ofReal_lt_ofReal_iff q.property).mp hq,
        (heqω _).mp hgood⟩
    · rw [ite_eq_right hgood] at hq
      exact False.elim ((not_lt_of_ge bot_le) hq)
  · rintro ⟨s, hts, hs⟩
    obtain ⟨q, htq, hqs⟩ := exists_rat_btwn hts
    let q' : Q := ⟨q, lt_trans ht htq⟩
    have hqinside : closure (cluster (μ ω) R z q) ⊆ ball 0 R :=
      (closure_mono (hmono q s R q'.property hqs.le hR z z.property)).trans hs
    have hgood : F ω (z, ⟨q', q'.property⟩) := (heqω _).mpr hqinside
    have hle : ENNReal.ofReal (q : ℝ) ≤ H ω z :=
      le_iSup_of_le q' (by simp [hgood, q'])
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff q'.property).mpr htq) hle

/-- Every half-disc centre has a positive finite field-local containment
horizon. Cluster mass is conserved and Hausdorff continuity holds through
that centre's own horizon, including its first boundary contact. The proposed
field-locality, affine-invariance and coordinate-change inputs await review. -/
theorem exists_fieldLocal_centre_horizons_with_continuity
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h53 : ClusterBoundaryMeasureZeroStmt.{u}) (h54 : RegularizedClusterHarmonicBallsStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u}) (h72 : ClusterTimeContinuityStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc) :
    ∃ H : Ω → (ball (0 : ℂ) 1 → ℝ≥0∞),
      Measurable[fieldSigmaAlgebra α₀ hC (ball 0 1)] H ∧
      ∀ᵐ ω ∂P, ∀ z : ball (0 : ℂ) 1, (z : ℂ) ∈ ball (0 : ℂ) (1 / 2) →
        0 < H ω z ∧ H ω z ≤ μ ω (ball 0 1) ∧ H ω z < ⊤ ∧
        (∀ t : ℝ, 0 < t → (ENNReal.ofReal t < H ω z ↔ ∃ s : ℝ, t < s ∧
          closure (cluster (μ ω) 1 z s) ⊆ ball 0 1)) ∧
        ∀ t ∈ Ioc (0 : ℝ) (H ω z).toReal,
          μ ω (cluster (μ ω) 1 z t) = ENNReal.ofReal t ∧
          ∀ ε : ℝ≥0∞, 0 < ε → ∀ᶠ s in 𝓝[Ioi (0 : ℝ)] t,
            hausdorffEDist (cluster (μ ω) 1 z s) (cluster (μ ω) 1 z t) < ε := by
  obtain ⟨H, hH, hchar⟩ := exists_fieldLocal_centre_containment_horizons
    hI2 hγ hγ2 hα hGFF hμ hloc (R := 1) zero_lt_one
  obtain ⟨U, _, hU⟩ := exists_fieldLocal_finite_containment_threshold
    hI2 h53 h54 h71 hγ hγ2 hα hGFF hμ hloc
  obtain ⟨βm, βp, hlocfin⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  have hm := clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  have hmon := clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  have hb := h53 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ
  have hc := ae_cluster_hausdorff_continuity_of_mass_eq hI2 h72 hAff hCC
    hγ hγ2 hα hGFF hμ
  refine ⟨H, hH, ?_⟩
  filter_upwards [hchar, hU, hlocfin, hm, hmon, hb, hc] with ω hcharω hUω hfin hmass hmono hboundary hcont
  let : IsLocallyFiniteMeasure (μ ω) := hfin.1
  intro z hz
  have hμfin : μ ω (ball (0 : ℂ) 1) < ⊤ :=
    lt_of_le_of_lt (measure_mono ball_subset_closedBall)
      ((isCompact_closedBall (0 : ℂ) 1).measure_lt_top)
  have hUpos : 0 < (U ω).toReal := ENNReal.toReal_pos hUω.1.ne' hUω.2.2.1.ne
  have hltU : ENNReal.ofReal ((U ω).toReal / 2) < U ω := by
    calc
      _ < ENNReal.ofReal (U ω).toReal :=
        (ENNReal.ofReal_lt_ofReal_iff hUpos).mpr (by linarith)
      _ = U ω := ENNReal.ofReal_toReal hUω.2.2.1.ne
  obtain ⟨T, hT, hinside⟩ := (hUω.2.2.2.1 _ (by linarith)).mp hltU
  have hbelow : ENNReal.ofReal ((U ω).toReal / 2) < H ω z := by
    apply (hcharω z _ (by linarith)).mpr
    obtain ⟨s, hlow, hsT⟩ := exists_between hT
    exact ⟨s, hlow, hinside z hz s ⟨by linarith, hsT⟩⟩
  have hpos : 0 < H ω z := lt_trans (ENNReal.ofReal_pos.mpr (by linarith)) hbelow
  have hbound : H ω z ≤ μ ω (ball (0 : ℂ) 1) := by
    by_contra hn
    obtain ⟨q, hqlo, hqhi⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp (lt_of_not_ge hn)
    have hqpos : 0 < (q : ℝ) := by
      have hqpos' : 0 < (q : ℝ≥0∞) := lt_of_le_of_lt bot_le hqlo
      exact_mod_cast hqpos'
    have hqhi' : ENNReal.ofReal (q : ℝ) < H ω z := by simpa using hqhi
    obtain ⟨s, hqs, hs⟩ := (hcharω z q hqpos).mp hqhi'
    have hcl : closure (cluster (μ ω) 1 z q) ⊆ ball 0 1 :=
      (closure_mono (hmono q s 1 hqpos hqs.le zero_lt_one z z.property)).trans hs
    have heq := (hmass 1 q zero_lt_one hqpos z z.property).2.2 hcl
      (hboundary z z.property q hqpos hcl)
    have hle : ENNReal.ofReal (q : ℝ) ≤ μ ω (ball (0 : ℂ) 1) := by
      rw [← heq]
      exact measure_mono cluster_subset_ball
    have hlo : μ ω (ball (0 : ℂ) 1) < ENNReal.ofReal (q : ℝ) := by simpa using hqlo
    exact (not_lt_of_ge hle) hlo
  have hfinite : H ω z < ⊤ := lt_of_le_of_lt hbound hμfin
  have hrealpos : 0 < (H ω z).toReal := ENNReal.toReal_pos hpos.ne' hfinite.ne
  refine ⟨hpos, hbound, hfinite, hcharω z, ?_⟩
  intro t ht
  have hmass_before : ∀ s ∈ Ioo (0 : ℝ) (H ω z).toReal,
      μ ω (cluster (μ ω) 1 z s) = ENNReal.ofReal s := by
    intro s hs
    have hsH : ENNReal.ofReal s < H ω z := by
      rw [← ENNReal.ofReal_toReal hfinite.ne]
      exact (ENNReal.ofReal_lt_ofReal_iff hrealpos).mpr hs.2
    obtain ⟨v, hsv, hv⟩ := (hcharω z s hs.1).mp hsH
    have hcl := (closure_mono (hmono s v 1 hs.1 hsv.le zero_lt_one z z.property)).trans hv
    exact (hmass 1 s zero_lt_one hs.1 z z.property).2.2 hcl
      (hboundary z z.property s hs.1 hcl)
  have heq : μ ω (cluster (μ ω) 1 z t) = ENNReal.ofReal t := by
    rcases lt_or_eq_of_le ht.2 with hlt | rfl
    · exact hmass_before t ⟨ht.1, hlt⟩
    · apply cluster_measure_eq_of_earlier_mass_eq (μ ω) 1 z hrealpos
      · intro s hs
        exact hmono s (H ω z).toReal 1 hs.1 hs.2.le zero_lt_one z z.property
      · exact (hmass 1 (H ω z).toReal zero_lt_one hrealpos z z.property).1
      · exact hmass_before
  exact ⟨heq, hcont z z.property t ht.1 heq⟩

end HarmonicBalls
