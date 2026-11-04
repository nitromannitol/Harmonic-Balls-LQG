import HarmonicBalls.Proofs.Sec9.JointMassRepresentatives

/-! # Entry time for a mass-parametrized subharmonic-ball family

The rational envelope has a measurable extended nonnegative entry time. Its
strict sublevel sets reproduce the envelope exactly and each original ball
almost everywhere. This constructs no new family of balls.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- The infimum of positive rational masses whose ball contains the point;
points in none of them have entry time infinity. -/
noncomputable def massEntryTime (A : ℝ → Set ℂ) (x : ℂ) : ℝ≥0∞ := by
  classical
  exact ⨅ q : {q : ℚ // 0 < (q : ℝ)}, if x ∈ A q.val then ENNReal.ofReal q.val else ∞

/-- Measurable rational sections give a measurable entry time. -/
theorem measurable_massEntryTime (A : ℝ → Set ℂ)
    (hA : ∀ q : ℚ, 0 < (q : ℝ) → MeasurableSet (A q)) :
    Measurable (massEntryTime A) := by
  classical
  unfold massEntryTime
  apply Measurable.iInf
  intro q
  exact Measurable.ite (hA q.val q.property) measurable_const measurable_const

/-- The strict sublevel at a positive mass is exactly the left rational
mass envelope, without any measure-theoretic assumptions. -/
theorem massEntryTime_lt_iff_mem_leftRationalMassEnvelope
    (A : ℝ → Set ℂ) {t : ℝ} (ht : 0 < t) (x : ℂ) :
    massEntryTime A x < ENNReal.ofReal t ↔ x ∈ leftRationalMassEnvelope A t := by
  classical
  rw [massEntryTime, iInf_lt_iff]
  simp only [leftRationalMassEnvelope, mem_iUnion]
  constructor
  · rintro ⟨q, hq⟩
    split_ifs at hq with hx
    · exact ⟨q.val, q.property, (ENNReal.ofReal_lt_ofReal_iff ht).mp hq, hx⟩
    · exact (not_lt_of_ge le_top hq).elim
  · rintro ⟨q, hq, hqt, hx⟩
    refine ⟨⟨q, hq⟩, ?_⟩
    simp only [hx, ↓reduceIte]
    exact (ENNReal.ofReal_lt_ofReal_iff ht).mpr hqt

universe u

/-- Under volume growth and typical scales, a bounded mass-parametrized
same-centre family admits a measurable entry time whose strict sublevels
agree almost everywhere with the balls and have mass equal to their time;
the entry-time pushforward has the same mass on every positive initial interval.
The agreement null set can depend on the time and the family. -/
theorem ae_massParametrized_subharmonicBall_entry_time
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : ℝ → Set ℂ) (z : ℂ),
      (∀ t : ℝ, 0 < t → Bornology.IsBounded (A t) ∧
        IsSubharmonicBall (μ ω) (A t) z ∧ μ ω (A t) = ENNReal.ofReal t) →
      ∃ τ : ℂ → ℝ≥0∞, Measurable τ ∧
        ∀ t : ℝ, 0 < t →
          (∀ᵐ x ∂(μ ω), (τ x < ENNReal.ofReal t ↔ x ∈ A t)) ∧
          μ ω {x | τ x < ENNReal.ofReal t} = ENNReal.ofReal t ∧
          Measure.map τ (μ ω) (Iio (ENNReal.ofReal t)) = ENNReal.ofReal t := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_bounded_subharmonicBall_order_by_mass hI2 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_bounded_subharmonicBall_eventually_mem_iff_of_monotone_mass_limit hI2 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω horder hconv
  intro A z hA
  have hmeas : ∀ q : ℚ, 0 < (q : ℝ) → MeasurableSet (A q) :=
    fun q hq => (hA q hq).2.1.1.measurableSet
  refine ⟨massEntryTime A, measurable_massEntryTime A hmeas, ?_⟩
  intro t ht
  have hall : ∀ᵐ x ∂(μ ω), ∀ q : ℚ, 0 < (q : ℝ) → (q : ℝ) < t → x ∈ A q → x ∈ A t := by
    apply ae_all_iff.mpr
    intro q
    by_cases hq : 0 < (q : ℝ) ∧ (q : ℝ) < t
    · have hn : μ ω (A q \ A t) = 0 := horder (A q) (A t) z
        (hA q hq.1).1 (hA t ht).1 (hA q hq.1).2.1 (hA t ht).2.1 (by
          rw [(hA q hq.1).2.2, (hA t ht).2.2]
          exact ENNReal.ofReal_le_ofReal hq.2.le)
      filter_upwards [measure_eq_zero_iff_ae_notMem.mp hn] with x hx _ _ hqx
      by_contra htx
      exact hx ⟨hqx, htx⟩
    · exact Filter.Eventually.of_forall fun _ hq0 hqt _ => (hq ⟨hq0, hqt⟩).elim
  obtain ⟨q, hqmono, hqt, hqtend⟩ := Real.exists_seq_rat_strictMono_tendsto t
  obtain ⟨N, hN⟩ := (eventually_atTop.mp (hqtend.eventually (Ioi_mem_nhds ht)))
  let q' : ℕ → ℚ := fun n => q (n + N)
  have hqpos : ∀ n, 0 < (q' n : ℝ) := fun n => hN (n + N) (by omega)
  have hqlt : ∀ n, (q' n : ℝ) < t := fun n => hqt (n + N)
  have hq'mono : Monotone (fun n => (q' n : ℝ)) := by
    intro n m hnm
    change (q (n + N) : ℝ) ≤ (q (m + N) : ℝ)
    exact_mod_cast hqmono.monotone (Nat.add_le_add_right hnm N)
  have hq'tend : Tendsto (fun n => (q' n : ℝ)) atTop (𝓝 t) :=
    hqtend.comp (tendsto_add_atTop_nat N)
  have hseq : ∀ n, Bornology.IsBounded (A (q' n)) ∧
      IsSubharmonicBall (μ ω) (A (q' n)) z :=
    fun n => ⟨(hA (q' n) (hqpos n)).1, (hA (q' n) (hqpos n)).2.1⟩
  have hmass : ∀ n, (μ ω (A (q' n))).toReal = (q' n : ℝ) := by
    intro n
    rw [(hA (q' n) (hqpos n)).2.2, ENNReal.toReal_ofReal (hqpos n).le]
  have htval : (μ ω (A t)).toReal = t := by
    rw [(hA t ht).2.2, ENNReal.toReal_ofReal ht.le]
  have hmon : Monotone (fun n => (μ ω (A (q' n))).toReal) := by
    simpa only [hmass] using hq'mono
  have hlim : Tendsto (fun n => (μ ω (A (q' n))).toReal) atTop
      (𝓝 ((μ ω (A t)).toReal)) := by
    simpa only [hmass, htval] using hq'tend
  have hpoint := hconv (fun n => A (q' n)) (A t) z hseq (hA t ht).1
    (hA t ht).2.1 hmon hlim
  have heq : ∀ᵐ x ∂(μ ω), (massEntryTime A x < ENNReal.ofReal t ↔ x ∈ A t) := by
    filter_upwards [hall, hpoint] with x hx hpoint
    rw [massEntryTime_lt_iff_mem_leftRationalMassEnvelope A ht x]
    constructor
    · intro hxB
      simp only [leftRationalMassEnvelope, mem_iUnion] at hxB
      obtain ⟨q, hq0, hqt, hmem⟩ := hxB
      exact hx q hq0 hqt hmem
    · intro hxt
      obtain ⟨n, hn⟩ := hpoint.exists
      exact mem_iUnion.mpr ⟨q' n, mem_iUnion.mpr ⟨hqpos n,
        mem_iUnion.mpr ⟨hqlt n, hn.mpr hxt⟩⟩⟩
  have hset : {x | massEntryTime A x < ENNReal.ofReal t} =ᵐ[μ ω] A t := by
    filter_upwards [heq] with x hx
    exact propext hx
  have hmass : μ ω {x | massEntryTime A x < ENNReal.ofReal t} = ENNReal.ofReal t := by
    rw [measure_congr hset, (hA t ht).2.2]
  refine ⟨heq, hmass, ?_⟩
  rw [Measure.map_apply (measurable_massEntryTime A hmeas) measurableSet_Iio]
  exact hmass

end HarmonicBalls
