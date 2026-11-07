import HarmonicBalls.Proofs.Sec8.ContinuityExhaustion
import HarmonicBalls.Proofs.Sec8.CenteredCircleLocal

/-! # Continuity radii for buffered local pinch data

The Section 8 construction used here imports Leonardo Bonanno's LatticeProb
formalization. The reference radius is chosen in a prescribed interval.
-/

open MeasureTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- A reference ball can be chosen between two prescribed radii, together
with an exhaustion by balls whose frontiers are almost surely LQG-null. -/
theorem IsWholePlaneGFF.exists_ae_lqg_continuity_exhaustion_between
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) {a ε : ℝ}
    (ha : 0 ≤ a) (haε : a < ε) :
    ∃ R ∈ Ioo a ε, ∃ r : ℕ → ℝ,
      StrictMono r ∧ (∀ n, r n ∈ Ioo (0 : ℝ) R) ∧
      Tendsto r atTop (𝓝 R) ∧
      (⋃ n, ball (0 : ℂ) (r n)) = ball 0 R ∧
      ∀ᵐ ω ∂P, (∀ n, μ ω (frontier (ball (0 : ℂ) (r n))) = 0) ∧
        μ ω (frontier (ball 0 R)) = 0 := by
  obtain ⟨q, hq, hzq⟩ := hGFF.exists_ae_lqg_null_frontier_balls_unbounded P hμ
    (fun _ => 0) (fun _ => a) (fun _ => ε) (fun _ => haε)
  let R := q 0
  have hR : R ∈ Ioo a ε := hq 0
  have hRpos : 0 < R := lt_of_le_of_lt ha hR.1
  obtain ⟨s, hsmono, hsrange, hslim⟩ := exists_seq_strictMono_tendsto' hRpos
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

/-- A buffered continuity system can be chosen to contain a prescribed
smaller ball while staying inside the field neighborhood. -/
theorem IsWholePlaneGFF.exists_ae_lqg_buffered_continuity_system_between
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) {a ε : ℝ}
    (ha : 0 ≤ a) (haε : a < ε) :
    ∃ (T : Set (Set ℂ)) (R : ℝ) (E : ℕ → Set ℂ),
      R ∈ Ioo a ε ∧ T.Countable ∧ IsPiSystem T ∧
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
    hGFF.exists_ae_lqg_continuity_exhaustion_between P hμ ha haε
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

/-- Centered local circle-average versions determine a normalized LQG
restriction on a reference ball containing any prescribed smaller ball. -/
theorem IsWholePlaneGFF.exists_normalizedRestriction_between_of_centered_versions
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : @Measure Ω mΩ)
    [IsProbabilityMeasure P] (m : MeasurableSpace Ω) (hm : m ≤ mΩ)
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : @IsWholePlaneGFF Ω mΩ P hC hcirc)
    (hμ : @IsLQGMeasureOfField Ω mΩ P γ α₀ hcirc μ)
    (hpositive : ∀ᵐ ω ∂P, ∀ R : ℝ, 0 < R →
      μ ω (ball 0 R) ≠ 0 ∧ μ ω (ball 0 R) ≠ ∞)
    {a ε : ℝ} (ha : 0 ≤ a) (haε : a < ε) :
    ∃ (R : ℝ) (E : ℕ → Set ℂ), R ∈ Ioo a ε ∧
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
    hGFF.exists_ae_lqg_buffered_continuity_system_between P hμ ha haε
  refine ⟨R, E, hR, hEunion, hbuffer, ?_⟩
  intro d hdm hdeq
  have hpos : ∀ᵐ ω ∂P, μ ω (ball 0 R) ≠ 0 ∧ μ ω (ball 0 R) ≠ ∞ :=
    hpositive.mono (fun _ h => h R (lt_of_le_of_lt ha hR.1))
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

/-- The normalized LQG masses on a prescribed smaller ball are measurable
from the field modulo constants on the larger neighborhood. -/
theorem IsWholePlaneGFF.exists_modConst_normalized_lqg_masses_between
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    {γ α₀ : ℝ} {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {μ : Ω → Measure ℂ} (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hfull : ∀ᵐ ω ∂P, ∀ U : Set ℂ, IsOpen U → U.Nonempty → 0 < μ ω U)
    {a ε : ℝ} (ha : 0 ≤ a) (haε : a < ε) :
    ∃ R ∈ Ioo a ε, ∃ ν : Ω → Measure ℂ,
      @Measurable Ω (Measure ℂ) (Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)) _ ν ∧
      ∀ᵐ ω ∂P,
        (μ ω (ball 0 R))⁻¹ ≠ 0 ∧ (μ ω (ball 0 R))⁻¹ ≠ ∞ ∧
        ∀ B : Set ℂ, MeasurableSet B → B ⊆ ball 0 R →
          ((μ ω (ball 0 R))⁻¹ • μ ω) B = ν ω B := by
  let : IsProbabilityMeasure P := hGFF.isProbabilityMeasure
  let m := Section6.fieldSigmaAlgebraModConst α₀ hC (ball 0 ε)
  let : MeasurableSpace Ω := mΩ
  have hm : m ≤ mΩ := (Section6.fieldSigmaAlgebraModConst_le α₀ hC _).trans
    (hGFF.fieldSigmaAlgebra_le α₀ _)
  have hloc : ∀ᵐ ω ∂P, IsLocallyFiniteMeasure (μ ω) := by
    filter_upwards [hμ] with ω hω
    exact hω.isLocallyFiniteMeasure
  have hpositive := ae_referenceBall_pos_finite P μ hfull hloc
  obtain ⟨R, E, hR, _, hbuffer, hversion⟩ :=
    hGFF.exists_normalizedRestriction_between_of_centered_versions P m hm hμ hpositive ha haε
  have hex : ∀ n : ℕ, ∃ d : Ω → ℂ → ℝ,
      @Measurable (Ω × ℂ) ℝ (m.prod inferInstance) _ (Function.uncurry d) ∧
      ∀ᵐ ω ∂P, ∀ z, closedBall z (dyadicScale n) ⊆ ball 0 ε →
        d ω z = fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) z -
          fieldCircleAverage α₀ (hcirc ω) (dyadicScale n) 0 := by
    intro n
    exact hGFF.exists_joint_centered_circle_version (α₀ := α₀) (ε := ε) (dyadicScale_pos n)
  choose d hdm hdeq using hex
  obtain ⟨ν, hν, hνeq⟩ := hversion d hdm (fun n => (hdeq n).mono fun ω hω z hz => hω z (hbuffer n z hz))
  refine ⟨R, hR, ν, hν, ?_⟩
  filter_upwards [hpositive, hνeq] with ω hpos heq
  obtain ⟨hne, htop⟩ := hpos R (lt_of_le_of_lt ha hR.1)
  refine ⟨ENNReal.inv_ne_zero.mpr htop, ENNReal.inv_ne_top.mpr hne, ?_⟩
  intro B hB hBR
  rw [heq, normalizedRestriction, Measure.smul_apply, Measure.smul_apply,
    Measure.restrict_apply hB, inter_eq_self_of_subset_left hBR]

#print axioms IsWholePlaneGFF.exists_ae_lqg_continuity_exhaustion_between
#print axioms IsWholePlaneGFF.exists_ae_lqg_buffered_continuity_system_between
#print axioms IsWholePlaneGFF.exists_normalizedRestriction_between_of_centered_versions
#print axioms IsWholePlaneGFF.exists_modConst_normalized_lqg_masses_between

end HarmonicBalls
