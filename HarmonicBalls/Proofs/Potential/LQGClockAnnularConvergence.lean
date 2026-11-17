import HarmonicBalls.Proofs.Potential.LQGClockAnnularSummability

/-! # Countable-time annular clock increments

Expected uniform bounds imply almost-sure summability on countable time sets.
-/

open MeasureTheory MarkovProcess Set Filter
open scoped ENNReal NNReal Interval Topology

namespace HarmonicBalls

/-- Uniform increments over any countable collection of unit times are summable
almost surely under the product law. -/
theorem exists_ae_tsum_countable_stoppedAnnularClock_iSup_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ)
    {ι : Type*} [Countable ι] (t : ι → Icc (0 : ℝ) 1) :
    ∃ K : ℕ, ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      (∑' j : ℕ, ⨆ i : ι, ENNReal.ofReal (|stoppedAnnularClock (fun z =>
        (dyadicScale (j+K+1))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K+1)) z)) δ
            (fun _ => ((t i : ℝ).toNNReal)) p.2 -
        stoppedAnnularClock (fun z => (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K)) z)) δ
            (fun _ => ((t i : ℝ).toNNReal)) p.2|)) < ⊤ := by
  obtain ⟨K, hK⟩ := exists_tsum_lintegral_prod_stoppedAnnularClock_iSup_lt_top hh x hγ hγ2 α hδ
  let S (j : ℕ) (p : Ω × ContinuousPath ℂ) := ⨆ i : ι, ENNReal.ofReal (|stoppedAnnularClock (fun z =>
        (dyadicScale (j+K+1))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K+1)) z)) δ
            (fun _ => ((t i : ℝ).toNNReal)) p.2 -
        stoppedAnnularClock (fun z => (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K)) z)) δ
            (fun _ => ((t i : ℝ).toNNReal)) p.2|)
  have hS (j : ℕ) : AEMeasurable (S j) (P.prod (planarBrownianMotion x)) := by
    apply AEMeasurable.iSup
    intro i
    exact ((aemeasurable_stoppedAnnularClock_sub hh x γ α δ
      (fun _ => ((t i : ℝ).toNNReal)) measurable_const (j+K)).abs).ennreal_ofReal
  have hint : (∫⁻ p, ∑' j, S j p ∂(P.prod (planarBrownianMotion x))) < ⊤ := by
    rw [lintegral_tsum hS]
    apply lt_of_le_of_lt _ hK
    apply ENNReal.tsum_le_tsum
    intro j
    apply lintegral_mono
    intro p
    dsimp only [S]
    apply iSup_le
    intro i
    exact le_iSup (fun u : Icc (0 : ℝ) 1 => ENNReal.ofReal (|stoppedAnnularClock (fun z =>
        (dyadicScale (j+K+1))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K+1)) z)) δ
            (fun _ => ((u : ℝ).toNNReal)) p.2 -
        stoppedAnnularClock (fun z => (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K)) z)) δ
            (fun _ => ((u : ℝ).toNNReal)) p.2|)) (t i)
  refine ⟨K, ?_⟩
  exact ae_lt_top' (AEMeasurable.tsum hS) hint.ne

/-- For a continuous density, the annular occupation clock is continuous in time. -/
theorem continuous_stoppedAnnularClock_time (f : ℂ → ℝ) (hf : Continuous f)
    (δ : ℝ) (b : ContinuousPath ℂ) :
    Continuous (fun t : ℝ => stoppedAnnularClock f δ (fun _ => t.toNNReal) b) := by
  let A : Set ℂ := {z | δ ≤ ‖z‖ ∧ ‖z‖ ≤ 1/2}
  let g : ℝ → ℝ := fun s => A.indicator f (b s.toNNReal)
  have hA : MeasurableSet A := (measurableSet_le measurable_const measurable_norm).inter
    (measurableSet_le measurable_norm measurable_const)
  have hgm : Measurable g := (hf.measurable.indicator hA).comp
    (b.continuous.measurable.comp continuous_real_toNNReal.measurable)
  obtain ⟨K, hK⟩ := (isCompact_closedBall (0 : ℂ) (1/2 : ℝ)).bddAbove_image hf.norm.continuousOn
  have hgK : ∀ s, ‖g s‖ ≤ max K 0 := by
    intro s
    by_cases hs : b s.toNNReal ∈ A
    · have hs' : b s.toNNReal ∈ Metric.closedBall (0 : ℂ) (1/2 : ℝ) := by
        simpa only [Metric.mem_closedBall, dist_zero_right] using hs.2
      rw [show g s = f (b s.toNNReal) from Set.indicator_of_mem hs _]
      exact (hK ⟨_, hs', rfl⟩).trans (le_max_left K 0)
    · rw [show g s = 0 from Set.indicator_of_notMem hs _, norm_zero]
      exact le_max_right K 0
  have hgi (a c : ℝ) : IntervalIntegrable g volume a c := by
    have hc : IntervalIntegrable (fun _ : ℝ => max K 0) volume a c := intervalIntegrable_const
    apply hc.mono_fun' hgm.aestronglyMeasurable.restrict
    exact Filter.Eventually.of_forall hgK
  have hc : Continuous (fun t : ℝ => ∫ s in (0 : ℝ)..t, g s) :=
    intervalIntegral.continuous_primitive hgi 0
  have ht : Continuous (fun t : ℝ => min (1 : ℝ) (max t 0)) :=
    continuous_const.min (continuous_id.max continuous_const)
  convert hc.comp ht using 1
  funext t
  rw [stoppedAnnularClock_eq_time_integral _ hf.measurable]
  simp only [NNReal.coe_one, Real.coe_toNNReal']
  rfl

/-- Every actual dyadic annular clock is continuous in time on one field event. -/
theorem ae_continuous_stoppedAnnularClock_time
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (γ α δ : ℝ) :
    ∀ᵐ ω ∂P, ∀ (k : ℕ) (b : ContinuousPath ℂ),
      Continuous (fun t : ℝ => stoppedAnnularClock (fun z => (dyadicScale k)^(γ^2/2) *
        Real.exp (γ * LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z)) δ
        (fun _ => t.toNNReal) b) := by
  obtain ⟨H, hHc, _, hHae⟩ := hh.exists_jointlyMeasurable_circleAverage
  filter_upwards [hHae, ae_recentered_inserted_circle_average hh α] with ω hω hrec
  intro k b
  have hc : Continuous (hcirc ω (dyadicScale k)) := by
    rw [← funext (hω (dyadicScale k))]
    exact hHc ω (dyadicScale k) (dyadicScale_pos k)
  have heq : (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) =
      fun z => hcirc ω (dyadicScale k) z - hcirc ω 1 0 - α * Real.log (max (dyadicScale k) ‖z‖) := by
    funext z
    exact (hrec _ z (dyadicScale_pos k)).symm
  have hci : Continuous (fun z => LatticeProb.Gauss.fieldCircleAverage α (hcirc ω) (dyadicScale k) z) := by
    rw [heq]
    exact (hc.sub continuous_const).sub (continuous_const.mul
      ((continuous_const.max continuous_norm).log
        (fun _ => (lt_max_of_lt_left (dyadicScale_pos k)).ne')))
  exact continuous_stoppedAnnularClock_time _
    (continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul hci))) δ b

private def rationalUnitTime (q : ℚ) : Icc (0 : ℝ) 1 :=
  ⟨min 1 (max (q : ℝ) 0), ⟨le_min (by norm_num) (le_max_right _ _), min_le_left _ _⟩⟩

private theorem iSup_unit_eq_rational (f : ℝ → ℝ≥0∞) (hf : Continuous f) :
    (⨆ t : Icc (0 : ℝ) 1, f t) = ⨆ q : ℚ, f (rationalUnitTime q) := by
  apply le_antisymm
  · apply iSup_le
    intro t
    have hc : Continuous (fun x : ℝ => f (min 1 (max x 0))) :=
      hf.comp (continuous_const.min (continuous_id.max continuous_const))
    have hclosed : IsClosed {x : ℝ | f (min 1 (max x 0)) ≤ ⨆ q : ℚ, f (rationalUnitTime q)} :=
      isClosed_le hc continuous_const
    have hall : ∀ x : ℝ, f (min 1 (max x 0)) ≤ ⨆ q : ℚ, f (rationalUnitTime q) := by
      intro x
      refine Rat.denseRange_cast.induction_on x hclosed ?_
      intro q
      exact le_iSup (fun q : ℚ => f (rationalUnitTime q)) q
    simpa only [max_eq_left t.property.1, min_eq_right t.property.2] using hall t
  · apply iSup_le
    intro q
    exact le_iSup (fun t : Icc (0 : ℝ) 1 => f t) (rationalUnitTime q)

/-- The actual uniform annular increments are summable almost surely. -/
theorem exists_ae_tsum_stoppedAnnularClock_iSup_lt_top
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      (∑' j : ℕ, ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal (|stoppedAnnularClock (fun z =>
        (dyadicScale (j+K+1))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K+1)) z)) δ
            (fun _ => ((t : ℝ).toNNReal)) p.2 -
        stoppedAnnularClock (fun z => (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
          LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K)) z)) δ
            (fun _ => ((t : ℝ).toNNReal)) p.2|)) < ⊤ := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  obtain ⟨K, hK⟩ := exists_ae_tsum_countable_stoppedAnnularClock_iSup_lt_top hh x hγ hγ2 α hδ rationalUnitTime
  refine ⟨K, ?_⟩
  filter_upwards [hK, (Measure.quasiMeasurePreserving_fst
    (μ := P) (ν := planarBrownianMotion x)).ae
      (ae_continuous_stoppedAnnularClock_time hh γ α δ)] with p hp hc
  convert hp using 1
  congr 1
  funext j
  let F : ℝ → ℝ := fun t => stoppedAnnularClock (fun z =>
    (dyadicScale (j+K+1))^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K+1)) z)) δ
        (fun _ => t.toNNReal) p.2 -
    stoppedAnnularClock (fun z => (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K)) z)) δ
        (fun _ => t.toNNReal) p.2
  change (⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |F t|) =
    ⨆ q : ℚ, ENNReal.ofReal |F (rationalUnitTime q)|
  exact iSup_unit_eq_rational (fun t => ENNReal.ofReal |F t|)
    (ENNReal.continuous_ofReal.comp (((hc (j+K+1) p.2).sub (hc (j+K) p.2)).abs))

/-- The fine-scale actual annular clocks converge uniformly on the unit interval
almost surely under the field-path product law. -/
theorem exists_ae_uniform_limit_stoppedAnnularClock
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : LatticeProb.Gauss.IsWholePlaneGFF P hC hcirc) (x : ℂ) {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ^2 < 2) (α : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∃ K : ℕ, ∀ᵐ p : Ω × ContinuousPath ℂ ∂(P.prod (planarBrownianMotion x)),
      ∃ F : Icc (0 : ℝ) 1 → ℝ, ∀ η : ℝ, 0 < η →
        ∀ᶠ j in atTop, ∀ t : Icc (0 : ℝ) 1,
          |stoppedAnnularClock (fun z => (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
            LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K)) z)) δ
              (fun _ => ((t : ℝ).toNNReal)) p.2 - F t| < η := by
  obtain ⟨K, hK⟩ := exists_ae_tsum_stoppedAnnularClock_iSup_lt_top hh x hγ hγ2 α hδ
  refine ⟨K, ?_⟩
  filter_upwards [hK] with p hp
  let A (j : ℕ) (t : Icc (0 : ℝ) 1) : ℝ := stoppedAnnularClock (fun z =>
    (dyadicScale (j+K))^(γ^2/2) * Real.exp (γ *
      LatticeProb.Gauss.fieldCircleAverage α (hcirc p.1) (dyadicScale (j+K)) z)) δ
        (fun _ => ((t : ℝ).toNNReal)) p.2
  let S (j : ℕ) : ℝ≥0∞ := ⨆ t : Icc (0 : ℝ) 1, ENNReal.ofReal |A (j+1) t - A j t|
  have hsum : (∑' j, S j) < ⊤ := by simpa only [S, A, Nat.add_assoc, Nat.add_comm K 1] using hp
  have hs : Summable (fun j => (S j).toReal) := ENNReal.summable_toReal hsum.ne
  have hfinite (j : ℕ) : S j ≠ ⊤ :=
    ne_top_of_le_ne_top hsum.ne (ENNReal.le_tsum j)
  have hbound (j : ℕ) (t : Icc (0 : ℝ) 1) : |A (j+1) t - A j t| ≤ (S j).toReal := by
    have h := ENNReal.toReal_mono (hfinite j) (le_iSup (fun t : Icc (0 : ℝ) 1 =>
      ENNReal.ofReal |A (j+1) t - A j t|) t)
    simpa only [ENNReal.toReal_ofReal (abs_nonneg _)] using h
  let F (t : Icc (0 : ℝ) 1) := atTop.limUnder (fun j => A j t)
  have hlim (t : Icc (0 : ℝ) 1) : Tendsto (fun j => A j t) atTop (𝓝 (F t)) := by
    have hc : CauchySeq (fun j => A j t) := by
      apply cauchySeq_of_dist_le_of_summable (fun j => (S j).toReal) _ hs
      intro j
      rw [Real.dist_eq, abs_sub_comm]
      exact hbound j t
    exact hc.tendsto_limUnder
  have htail (j : ℕ) (t : Icc (0 : ℝ) 1) :
      |A j t - F t| ≤ ∑' n, (S (j+n)).toReal := by
    have hd : ∀ n, dist (A n t) (A (n+1) t) ≤ (S n).toReal := by
      intro n
      rw [Real.dist_eq, abs_sub_comm]
      exact hbound n t
    simpa only [Real.dist_eq] using
      dist_le_tsum_of_dist_le_of_tendsto (fun n => (S n).toReal) hd hs (hlim t) j
  refine ⟨F, ?_⟩
  intro η hη
  have htend : Tendsto (fun j => ∑' n, (S (j+n)).toReal) atTop (𝓝 0) := by
    simpa only [Nat.add_comm] using tendsto_sum_nat_add (fun j => (S j).toReal)
  filter_upwards [htend.eventually (Iio_mem_nhds hη)] with j hj t
  exact (htail j t).trans_lt hj

end HarmonicBalls
