import HarmonicBalls.Proofs.Sec5.MeasureLawRegularity
import HarmonicBalls.Steps.Sec2.VolumeGrowth
import HarmonicBalls.Proofs.Sec5.CountableCentreContainment

/-! # Recovering volume growth from countable ball tests -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter TopologicalSpace
open scoped ENNReal

/-- Dyadic ball bounds on a dense family of centres imply bounds at every
centre, with a smaller ball for the lower bound and a larger ball for the upper bound. -/
theorem dense_dyadic_ball_bounds_all_centres
    {R βm βp : ℝ} {ν : Measure ℂ} (e : ℕ → ball (0 : ℂ) R) (he : DenseRange e)
    {N : ℕ} (hbound : ∀ n ≥ N, ∀ i,
      ENNReal.ofReal (dyadicScale n ^ βm) ≤ ν (ball (e i) (dyadicScale n)) ∧
      ν (ball (e i) (dyadicScale n)) ≤ ENNReal.ofReal (dyadicScale n ^ βp)) :
    ∀ k ≥ N, ∀ z ∈ ball (0 : ℂ) R,
      ENNReal.ofReal (dyadicScale (k + 2) ^ βm) ≤ ν (ball z (dyadicScale (k + 1))) ∧
      ν (ball z (dyadicScale (k + 1))) ≤ ENNReal.ofReal (dyadicScale k ^ βp) := by
  intro k hk z hz
  let d := dyadicScale (k + 1)
  have hd : 0 < d := dyadicScale_pos _
  obtain ⟨i, hi⟩ := (Metric.denseRange_iff.mp he) ⟨z, hz⟩ (d / 4) (by positivity)
  have hid : dist z (e i : ℂ) < d / 4 := by simpa [Subtype.dist_eq] using hi
  have hhalf : dyadicScale (k + 2) = d / 2 := by
    dsimp [d, dyadicScale]
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    ring
  have hdouble : dyadicScale k = 2 * d := by
    dsimp [d, dyadicScale]
    rw [pow_succ]
    ring
  have hlo : ball (e i : ℂ) (dyadicScale (k + 2)) ⊆ ball z d := by
    apply ball_subset_ball'
    rw [hhalf, dist_comm]
    linarith
  have hhi : ball z d ⊆ ball (e i : ℂ) (dyadicScale k) := by
    apply ball_subset_ball'
    rw [hdouble]
    linarith
  exact ⟨(hbound (k + 2) (by omega) i).1.trans (measure_mono hlo),
    (measure_mono hhi).trans (hbound k hk i).2⟩

/-- After allowing slack in the exponents, dense-centre dyadic bounds hold
at the same dyadic scale for every centre. -/
theorem dense_dyadic_ball_bounds_with_slack
    {R βm βp a b : ℝ} {ν : Measure ℂ} (e : ℕ → ball (0 : ℂ) R) (he : DenseRange e)
    (hab : a < βp) (hba : βm < b)
    {N : ℕ} (hbound : ∀ n ≥ N, ∀ i,
      ENNReal.ofReal (dyadicScale n ^ βm) ≤ ν (ball (e i) (dyadicScale n)) ∧
      ν (ball (e i) (dyadicScale n)) ≤ ENNReal.ofReal (dyadicScale n ^ βp)) :
    ∃ M : ℕ, ∀ n ≥ M, ∀ z ∈ ball (0 : ℂ) R,
      ENNReal.ofReal (dyadicScale n ^ b) ≤ ν (ball z (dyadicScale n)) ∧
      ν (ball z (dyadicScale n)) ≤ ENNReal.ofReal (dyadicScale n ^ a) := by
  obtain ⟨r₁, hr₁, h₁⟩ := exists_pos_forall_rpow_le (sub_pos.mpr hab)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2⁻¹) a)
  obtain ⟨r₂, hr₂, h₂⟩ := exists_pos_forall_rpow_le (sub_pos.mpr hba)
    (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2⁻¹) βm)
  have hsmall : ∀ᶠ k in atTop, dyadicScale k < min r₁ r₂ :=
    (tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds (lt_min hr₁ hr₂))
  obtain ⟨K, hK⟩ := eventually_atTop.mp hsmall
  refine ⟨max N K + 1, ?_⟩
  intro n hn z hz
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hkN : N ≤ k := by omega
  have hkK : K ≤ k := by omega
  have hdk : 0 < dyadicScale k := dyadicScale_pos k
  have hdn : 0 < dyadicScale (k + 1) := dyadicScale_pos _
  have hhalf : dyadicScale (k + 1) = (2 : ℝ)⁻¹ * dyadicScale k := by
    dsimp [dyadicScale]
    rw [pow_succ]
    ring
  have hhalf' : dyadicScale (k + 2) = (2 : ℝ)⁻¹ * dyadicScale (k + 1) := by
    dsimp [dyadicScale]
    rw [show k + 2 = (k + 1) + 1 by omega, pow_succ]
    ring
  have hdnsmall : dyadicScale (k + 1) < r₂ := by
    have := hK k hkK
    rw [hhalf]
    linarith [min_le_right r₁ r₂]
  have hksmall : dyadicScale k < r₁ := (hK k hkK).trans_le (min_le_left r₁ r₂)
  obtain ⟨hlow, hupp⟩ := dense_dyadic_ball_bounds_all_centres e he hbound k hkN z hz
  refine ⟨?_, ?_⟩
  · have hle : dyadicScale (k + 1) ^ b ≤ dyadicScale (k + 2) ^ βm := by
      calc dyadicScale (k + 1) ^ b =
          dyadicScale (k + 1) ^ (b - βm) * dyadicScale (k + 1) ^ βm := by
            rw [← Real.rpow_add hdn, sub_add_cancel]
        _ ≤ (2⁻¹ : ℝ) ^ βm * dyadicScale (k + 1) ^ βm := by
          gcongr
          exact h₂ _ hdn hdnsmall
        _ = dyadicScale (k + 2) ^ βm := by
          rw [hhalf', Real.mul_rpow (by norm_num) hdn.le]
    exact (ENNReal.ofReal_le_ofReal hle).trans hlow
  · have hle : dyadicScale k ^ βp ≤ dyadicScale (k + 1) ^ a := by
      calc dyadicScale k ^ βp = dyadicScale k ^ (βp - a) * dyadicScale k ^ a := by
            rw [← Real.rpow_add hdk, sub_add_cancel]
        _ ≤ (2⁻¹ : ℝ) ^ a * dyadicScale k ^ a := by
          gcongr
          exact h₁ _ hdk hksmall
        _ = dyadicScale (k + 1) ^ a := by
          rw [hhalf, Real.mul_rpow (by norm_num) hdk.le]
    exact hupp.trans (ENNReal.ofReal_le_ofReal hle)

/-- Dense-centre dyadic bounds with positive exponents imply the usual
volume-growth condition, after widening the exponents. -/
theorem volumeGrowth_of_dense_dyadic_ball_bounds
    {R βm βp : ℝ} {ν : Measure ℂ} (e : ℕ → ball (0 : ℂ) R) (he : DenseRange e)
    (hβm : 0 < βm) (hβp : 0 < βp)
    {N : ℕ} (hbound : ∀ n ≥ N, ∀ i,
      ENNReal.ofReal (dyadicScale n ^ βm) ≤ ν (ball (e i) (dyadicScale n)) ∧
      ν (ball (e i) (dyadicScale n)) ≤ ENNReal.ofReal (dyadicScale n ^ βp)) :
    VolumeGrowth ν R (βm + 2) (βp / 4) := by
  obtain ⟨M, hM⟩ := dense_dyadic_ball_bounds_with_slack e he
    (show βp / 2 < βp by linarith) (show βm < βm + 1 by linarith) hbound
  obtain ⟨r₁, hr₁, hwin⟩ := ballMassBoundEvent_window (fun _ : Unit => ν)
    (R := R) (a := βp / 4) (b := βm + 2) (βplus := βp / 2) (βminus := βm + 1)
    (by positivity) (by linarith) (by positivity) (by linarith)
  have hsmall : ∀ᶠ k in atTop, dyadicScale k < r₁ :=
    (tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds).eventually (Iio_mem_nhds hr₁)
  obtain ⟨K, hK⟩ := eventually_atTop.mp hsmall
  let L := max M K
  refine ⟨by positivity, by positivity, dyadicScale L, dyadicScale_pos L, ?_⟩
  intro r hr hrL z hz
  have hLone : dyadicScale L ≤ 1 := by
    unfold dyadicScale
    exact pow_le_one₀ (by norm_num) (by norm_num)
  obtain ⟨k, hk1, hk2⟩ := exists_nat_pow_near_of_lt_one hr
    (hrL.le.trans hLone) (by norm_num : (0 : ℝ) < 2⁻¹)
    (by norm_num : (2 : ℝ)⁻¹ < 1)
  have hkL : L ≤ k := by
    by_contra hlt
    have h' : k + 1 ≤ L := by omega
    have hp := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by norm_num : (2 : ℝ)⁻¹ ≤ 1) h'
    dsimp [dyadicScale] at hrL
    linarith
  have hkM : M ≤ k := (le_max_left M K).trans hkL
  have hkK : K ≤ k := (le_max_right M K).trans hkL
  have hleft : () ∈ ballMassBoundEvent (fun _ : Unit => ν) R (βp / 2) (βm + 1) (dyadicScale k) :=
    hM k hkM
  have hright : () ∈ ballMassBoundEvent (fun _ : Unit => ν) R (βp / 2) (βm + 1)
      ((2 : ℝ)⁻¹ * dyadicScale k) := by
    have h := hM (k + 1) (by omega)
    simpa only [ballMassBoundEvent, mem_ofPred_eq, dyadicScale, pow_succ, mul_comm] using h
  have hsmallk : dyadicScale k < r₁ := hK k hkK
  have hrlo : (2 : ℝ)⁻¹ * dyadicScale k ≤ r := by
    dsimp [dyadicScale]
    rw [pow_succ] at hk1
    linarith
  have hrhi : r ≤ dyadicScale k := by simpa [dyadicScale] using hk2
  exact hwin (dyadicScale k) (dyadicScale_pos k) hsmallk ⟨hleft, hright⟩ r hrlo hrhi z hz

universe u

/-- The law of an LQG measure is concentrated on a measurable set of locally
finite measures satisfying volume growth on a prescribed disc. -/
theorem IsWholePlaneGFF.exists_measurable_volumeGrowth_support
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {R : ℝ} (hR : 0 < R) :
    ∃ E : Set (Measure ℂ), MeasurableSet E ∧
      (∀ᵐ ν ∂Measure.map μ P, ν ∈ E) ∧
      ∀ ν ∈ E, IsLocallyFiniteMeasure ν ∧ ∃ βm βp, VolumeGrowth ν R βm βp := by
  let : Nonempty (ball (0 : ℂ) R) := ⟨⟨0, by simpa using hR⟩⟩
  let e : ℕ → ball (0 : ℂ) R := denseSeq _
  obtain ⟨βm, βp, hβm, hβp, hdyad⟩ :=
    hGFF.ae_dyadic_ball_bounds_lqgMeasureLaw hI2 hγ hγ2 hα hμ hR
      (fun i : ULift.{u} ℕ => e i.down)
  let E : Set (Measure ℂ) := {ν | IsLocallyFiniteMeasure ν} ∩
    {ν | ∃ N : ℕ, ∀ n ≥ N, ∀ i : ℕ,
      ENNReal.ofReal (dyadicScale n ^ βm) ≤ ν (ball (e i) (dyadicScale n)) ∧
      ν (ball (e i) (dyadicScale n)) ≤ ENNReal.ofReal (dyadicScale n ^ βp)}
  refine ⟨E, measurableSet_isLocallyFiniteMeasure_complex.inter
    (measurableSet_eventually_dyadic_ball_bounds (fun i => (e i : ℂ)) βm βp), ?_, ?_⟩
  · filter_upwards [hGFF.ae_isLocallyFiniteMeasure_lqgMeasureLaw hμ, hdyad] with ν hloc hdyadν
    obtain ⟨N, hN⟩ := hdyadν
    exact ⟨hloc, N, fun n hn i => hN n hn (ULift.up i)⟩
  · intro ν hν
    obtain ⟨N, hN⟩ := hν.2
    exact ⟨hν.1, βm + 2, βp / 4,
      volumeGrowth_of_dense_dyadic_ball_bounds e (denseRange_denseSeq _) hβm hβp hN⟩

/-- Local finiteness together with volume growth is null measurable under
the LQG measure law. -/
theorem IsWholePlaneGFF.nullMeasurableSet_volumeGrowth_measureLaw
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {R : ℝ} (hR : 0 < R) :
    NullMeasurableSet {ν : Measure ℂ | IsLocallyFiniteMeasure ν ∧
      ∃ βm βp, VolumeGrowth ν R βm βp} (Measure.map μ P) := by
  obtain ⟨G, hG, hGae, hGgood⟩ := hGFF.exists_measurable_volumeGrowth_support
    hI2 hγ hγ2 hα hμ hR
  apply hG.nullMeasurableSet.congr
  filter_upwards [hGae] with ν hν
  exact propext ⟨hGgood ν, fun _ => hν⟩

/-- For an LQG measure law, membership in a fixed cluster is null measurable
as a set of measures. -/
theorem IsWholePlaneGFF.nullMeasurableSet_cluster_measureLaw
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {R t : ℝ} {z x : ℂ} (hR : 0 < R) (hz : z ∈ ball (0 : ℂ) R) (ht : 0 < t) :
    NullMeasurableSet {ν : Measure ℂ | x ∈ cluster ν R z t} (Measure.map μ P) := by
  obtain ⟨G, _hG, hGae, hGgood⟩ := hGFF.exists_measurable_volumeGrowth_support
    hI2 hγ hγ2 hα hμ hR
  obtain ⟨E, hE, hgood⟩ := exists_measurableSet_mem_cluster_of_volumeGrowth hR hz ht (x := x)
  apply hE.nullMeasurableSet.congr
  filter_upwards [hGae] with ν hν
  exact propext (hgood ν (hGgood ν hν).1 (hGgood ν hν).2)

/-- Compact containment at countably many centres is null measurable under
the LQG measure law. -/
theorem IsWholePlaneGFF.nullMeasurableSet_countableCentre_containment_measureLaw
    {Ω : Type u} {ι : Type*} [MeasurableSpace Ω] [Countable ι]
    {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    {R : ℝ} (hR : 0 < R) (e : ι → ball (0 : ℂ) R) (T : ℝ) :
    NullMeasurableSet {ν : Measure ℂ | ∀ i, ∀ t ∈ Ioo (0 : ℝ) T,
      closure (cluster ν R (e i) t) ⊆ ball 0 R} (Measure.map μ P) := by
  obtain ⟨G, _hG, hGae, hGgood⟩ := hGFF.exists_measurable_volumeGrowth_support
    hI2 hγ hγ2 hα hμ hR
  obtain ⟨E, hE, hgood⟩ := exists_measurableSet_countableCentre_containment hR e T
  apply hE.nullMeasurableSet.congr
  filter_upwards [hGae] with ν hν
  obtain ⟨hloc, βm, βp, hvol⟩ := hGgood ν hν
  apply propext
  apply hgood ν hloc ⟨βm, βp, hvol⟩
  · intro i s hs
    exact (cluster_open_laplacian_of_general greenFunctionBall
      obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
      obstacleCompatibilityShiftStep_holds hloc hR hvol (e i).property hs).1
  · intro i s s' hs hss
    exact cluster_subset_of_general obstacleMonotoneGeneral_holds obstacleCompatibilityShiftStep_holds
      hloc hR hvol (e i).property hs hss

/-- Uniform closed-disc buffered containment is null measurable under the
LQG measure law. -/
theorem IsWholePlaneGFF.nullMeasurableSet_uniform_buffered_containment_measureLaw
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (ρ T : ℝ) :
    NullMeasurableSet {ν : Measure ℂ | ∀ z ∈ ball (0 : ℂ) (1 / 2), ∀ t ∈ Ioo (0 : ℝ) T,
      closure (cluster ν 1 z t) ⊆ closedBall 0 ρ} (Measure.map μ P) := by
  obtain ⟨G, _hG, hGae, hGgood⟩ := hGFF.exists_measurable_volumeGrowth_support
    hI2 hγ hγ2 hα hμ zero_lt_one
  obtain ⟨E, hE, hgood⟩ := exists_measurableSet_uniform_buffered_containment ρ T
  apply hE.nullMeasurableSet.congr
  filter_upwards [hGae] with ν hν
  obtain ⟨hloc, βm, βp, hvol⟩ := hGgood ν hν
  apply propext
  apply hgood ν hloc ⟨βm, βp, hvol⟩
  · intro z hz s hs
    have hz' : z ∈ ball (0 : ℂ) 1 := ball_subset_ball (by norm_num) hz
    exact (cluster_open_laplacian_of_general greenFunctionBall
      obstacleNonCoincidenceHarmonicGeneral_holds shiftedOdometerLaplacianGeneral_holds
      obstacleCompatibilityShiftStep_holds hloc zero_lt_one hvol hz' hs).1
  · intro z hz s s' hs hss
    have hz' : z ∈ ball (0 : ℂ) 1 := ball_subset_ball (by norm_num) hz
    exact cluster_subset_of_general obstacleMonotoneGeneral_holds obstacleCompatibilityShiftStep_holds
      hloc zero_lt_one hvol hz' hs hss

end HarmonicBalls
