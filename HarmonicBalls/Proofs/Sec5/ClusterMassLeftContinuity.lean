import HarmonicBalls.Proofs.Sec5.ClusterMassJump
import HarmonicBalls.Proofs.Sec5.CountableTimeMeasurability
import HarmonicBalls.Proofs.Sec3.ConservationOfMassLemma
import HarmonicBalls.Proofs.Sec5.MassSaturationContinuity

/-! # Left continuity of cluster mass

Every point of a cluster has already entered at an earlier rational time.
Monotonicity and continuity from below therefore imply left continuity of its
mass, independently of boundary contact or finiteness of the measure.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped Topology ENNReal Pointwise

/-- A positive-time cluster is the directed union of its clusters at earlier
positive rational times. -/
theorem cluster_eq_iUnion_earlier_rational
    {μ : Measure ℂ} {r t : ℝ} {z : ℂ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → cluster μ r z s ⊆ cluster μ r z s') :
    cluster μ r z t = ⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < t}, cluster μ r z q := by
  ext x
  constructor
  · intro hx
    obtain ⟨q, hq0, hqt, hxq⟩ := mem_cluster_exists_earlier_rat ht hx
    exact Set.mem_iUnion.mpr ⟨⟨q, hq0, hqt⟩, hxq⟩
  · intro hx
    obtain ⟨q, hxq⟩ := Set.mem_iUnion.mp hx
    exact hmono q t q.property.1 q.property.2.le hxq

/-- The mass of a positive-time cluster is the supremum of its masses at
earlier positive rational times. -/
theorem measure_cluster_eq_iSup_earlier_rational
    {μ : Measure ℂ} {r t : ℝ} {z : ℂ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → cluster μ r z s ⊆ cluster μ r z s') :
    μ (cluster μ r z t) =
      ⨆ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < t}, μ (cluster μ r z q) := by
  let F : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < t} → Set ℂ := fun q => cluster μ r z q
  have hd : Directed (· ⊆ ·) F := by
    intro a b
    let c : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < t} := ⟨max a b, by
      simp only [Rat.cast_max]
      exact ⟨lt_of_lt_of_le a.property.1 (le_max_left _ _), max_lt a.property.2 b.property.2⟩⟩
    refine ⟨c, ?_, ?_⟩
    · exact hmono a c a.property.1 (by exact_mod_cast le_max_left (a : ℚ) (b : ℚ))
    · exact hmono b c b.property.1 (by exact_mod_cast le_max_right (a : ℚ) (b : ℚ))
  rw [cluster_eq_iUnion_earlier_rational ht hmono]
  exact hd.measure_iUnion

/-- For an increasing disc-cluster family, cluster mass is left-continuous at
every positive time, without a compact-containment or finite-mass assumption. -/
theorem tendsto_measure_cluster_nhdsLT
    {μ : Measure ℂ} {r t : ℝ} {z : ℂ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → cluster μ r z s ⊆ cluster μ r z s') :
    Tendsto (fun s : ℝ => μ (cluster μ r z s)) (𝓝[<] t) (𝓝 (μ (cluster μ r z t))) := by
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    rw [measure_cluster_eq_iSup_earlier_rational ht hmono] at ha
    obtain ⟨q, hq⟩ := lt_iSup_iff.mp ha
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds q.property.2)] with s hs
    exact lt_of_lt_of_le hq (measure_mono (hmono q s q.property.1 hs.le))
  · intro a ha
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds ht),
      self_mem_nhdsWithin] with s hs0 hst
    exact lt_of_le_of_lt (measure_mono (hmono s t hs0 hst.le)) ha

/-- If the mass at the reference time is finite, the mass deficit is also
continuous from the left. -/
theorem tendsto_cluster_mass_deficit_nhdsLT
    {μ : Measure ℂ} {r t : ℝ} {z : ℂ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → cluster μ r z s ⊆ cluster μ r z s')
    (hfinite : μ (cluster μ r z t) ≠ ⊤) :
    Tendsto (fun s : ℝ => s - (μ (cluster μ r z s)).toReal) (𝓝[<] t)
      (𝓝 (t - (μ (cluster μ r z t)).toReal)) := by
  have hmass := (ENNReal.tendsto_toReal hfinite).comp (tendsto_measure_cluster_nhdsLT ht hmono)
  exact (continuousAt_id.tendsto.mono_left nhdsWithin_le_nhds).sub hmass

/-- A strict mass deficit persists throughout a left neighbourhood: the
first strict deficit cannot occur as a jump from earlier full-mass times. -/
theorem eventually_cluster_mass_deficit_nhdsLT
    {μ : Measure ℂ} {r t : ℝ} {z : ℂ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → cluster μ r z s ⊆ cluster μ r z s')
    (hdef : μ (cluster μ r z t) < ENNReal.ofReal t) :
    ∀ᶠ s : ℝ in 𝓝[<] t, 0 < s ∧ μ (cluster μ r z s) < ENNReal.ofReal s := by
  have hfinite : μ (cluster μ r z t) ≠ ⊤ :=
    ne_top_of_lt (lt_of_lt_of_le hdef le_top)
  have hreal : (μ (cluster μ r z t)).toReal < t := by
    have h := (ENNReal.toReal_lt_toReal hfinite ENNReal.ofReal_ne_top).2 hdef
    simpa [ENNReal.toReal_ofReal ht.le] using h
  have hpositive : 0 < t - (μ (cluster μ r z t)).toReal := sub_pos.mpr hreal
  have hnear := (tendsto_cluster_mass_deficit_nhdsLT ht hmono hfinite).eventually
    (Ioi_mem_nhds hpositive)
  filter_upwards [hnear, eventually_nhdsWithin_of_eventually_nhds (Ioi_mem_nhds ht),
    self_mem_nhdsWithin] with s hs hs0 hst
  refine ⟨hs0, ?_⟩
  have hfin_s : μ (cluster μ r z s) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinite (measure_mono (hmono s t hs0 hst.le))
  have hlt : ENNReal.ofReal ((μ (cluster μ r z s)).toReal) < ENNReal.ofReal s :=
    (ENNReal.ofReal_lt_ofReal_iff hs0).2 (sub_pos.mp hs)
  simpa [ENNReal.ofReal_toReal hfin_s] using hlt

universe u

/-- Almost surely, for all radii, centres and positive times, both the
cluster mass and its finite mass deficit are continuous from the left. -/
theorem ae_cluster_mass_and_deficit_left_continuity
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hγ : 0 < γ) (hγ2 : γ < 2)
    (hα : α₀ < lqgQ γ) (hGFF : IsWholePlaneGFF P hC hcirc)
    (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ r : ℝ, 0 < r → ∀ z ∈ ball (0 : ℂ) r, ∀ t : ℝ, 0 < t →
      Tendsto (fun s : ℝ => μ ω (cluster (μ ω) r z s)) (𝓝[<] t)
        (𝓝 (μ ω (cluster (μ ω) r z t))) ∧
      Tendsto (fun s : ℝ => s - (μ ω (cluster (μ ω) r z s)).toReal) (𝓝[<] t)
        (𝓝 (t - (μ ω (cluster (μ ω) r z t)).toReal)) := by
  filter_upwards [clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
    with ω hmono hmass
  intro r hr z hz t ht
  have hm : ∀ s s', 0 < s → s ≤ s' → cluster (μ ω) r z s ⊆ cluster (μ ω) r z s' :=
    fun s s' hs hss => hmono s s' r hs hss hr z hz
  have hfinite : μ ω (cluster (μ ω) r z t) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hmass r t hr ht z hz).1
  exact ⟨tendsto_measure_cluster_nhdsLT ht hm, tendsto_cluster_mass_deficit_nhdsLT ht hm hfinite⟩

/-- Any right-continuity failure is preceded by a left neighbourhood of
strict mass deficit. The affine inputs are staged pending source review. -/
theorem ae_cluster_right_discontinuity_has_earlier_mass_deficit
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (h72 : ClusterTimeContinuityStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      (¬ ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε) →
      ∀ᶠ s : ℝ in 𝓝[<] t, 0 < s ∧ μ ω (cluster (μ ω) 1 z s) < ENNReal.ofReal s := by
  filter_upwards [clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_mass_deficit_of_not_cluster_right_continuity hI2 h72 hAff hCC hγ hγ2 hα hGFF hμ]
    with ω hmono hdef
  intro z hz t ht hfail
  apply eventually_cluster_mass_deficit_nhdsLT ht
    (fun s s' hs hss => hmono s s' 1 hs hss zero_lt_one z hz)
  exact hdef z hz t ht hfail

end HarmonicBalls
