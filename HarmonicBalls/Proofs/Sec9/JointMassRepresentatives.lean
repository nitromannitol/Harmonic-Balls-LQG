import HarmonicBalls.Proofs.Sec9.GlobalMassContinuity
import Mathlib.Topology.Instances.Real.Lemmas

/-! # Jointly measurable monotone mass representatives -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

/-- The left rational envelope of a mass-indexed family. -/
def leftRationalMassEnvelope (A : ℝ → Set ℂ) (t : ℝ) : Set ℂ :=
  ⋃ q : ℚ, ⋃ (_ : 0 < (q : ℝ)), ⋃ (_ : (q : ℝ) < t), A q

/-- The envelope increases pointwise with mass. -/
theorem leftRationalMassEnvelope_mono (A : ℝ → Set ℂ) :
    Monotone (leftRationalMassEnvelope A) := by
  intro s t hst x hx
  simp only [leftRationalMassEnvelope, mem_iUnion] at hx ⊢
  obtain ⟨q, hq, hqs, hx⟩ := hx
  exact ⟨q, hq, lt_of_lt_of_le hqs hst, hx⟩

/-- Rational sections suffice for joint Borel measurability of the envelope. -/
theorem measurableSet_leftRationalMassEnvelope
    (A : ℝ → Set ℂ) (hA : ∀ q : ℚ, 0 < (q : ℝ) → MeasurableSet (A q)) :
    MeasurableSet {p : ℝ × ℂ | p.2 ∈ leftRationalMassEnvelope A p.1} := by
  have heq : {p : ℝ × ℂ | p.2 ∈ leftRationalMassEnvelope A p.1} =
      ⋃ q : ℚ, ⋃ (_ : 0 < (q : ℝ)), (Ioi (q : ℝ)).prod (A q) := by
    ext ⟨t, x⟩
    simp only [mem_ofPred_eq, leftRationalMassEnvelope, mem_iUnion]
    constructor
    · rintro ⟨q, hq, hqt, hx⟩
      exact ⟨q, hq, ⟨hqt, hx⟩⟩
    · rintro ⟨q, hq, hqt, hx⟩
      exact ⟨q, hq, hqt, hx⟩
  rw [heq]
  exact MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq =>
    measurableSet_Ioi.prod (hA q hq)

universe u

/-- On one probability-one event, the rational envelope is jointly Borel,
monotone, and agrees almost everywhere at each positive time with any family
of bounded same-centre subharmonic balls parametrized by their LQG mass.
The spatial null set of agreement may depend on the time and family. -/
theorem ae_massParametrized_subharmonicBall_has_joint_monotone_representative
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ α₀ : ℝ, 0 < γ → γ < 2 → α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ (A : ℝ → Set ℂ) (z : ℂ),
      (∀ t : ℝ, 0 < t → Bornology.IsBounded (A t) ∧
        IsSubharmonicBall (μ ω) (A t) z ∧ μ ω (A t) = ENNReal.ofReal t) →
      ∃ B : ℝ → Set ℂ, Monotone B ∧
        MeasurableSet {p : ℝ × ℂ | p.2 ∈ B p.1} ∧
        ∀ t : ℝ, 0 < t → ∀ᵐ x ∂(μ ω), (x ∈ B t ↔ x ∈ A t) := by
  intro γ α₀ hγ hγ2 hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_bounded_subharmonicBall_order_by_mass hI2 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_bounded_subharmonicBall_eventually_mem_iff_of_monotone_mass_limit hI2 h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω horder hconv
  intro A z hA
  let B : ℝ → Set ℂ := leftRationalMassEnvelope A
  have hmeas : ∀ q : ℚ, 0 < (q : ℝ) → MeasurableSet (A q) := by
    intro q hq
    exact (hA q hq).2.1.1.measurableSet
  have hBmeas : MeasurableSet {p : ℝ × ℂ | p.2 ∈ B p.1} :=
    measurableSet_leftRationalMassEnvelope A hmeas
  refine ⟨B, leftRationalMassEnvelope_mono A, hBmeas, ?_⟩
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
  have hqpos : ∀ n, 0 < (q' n : ℝ) := by
    intro n
    exact hN (n + N) (by omega)
  have hqlt : ∀ n, (q' n : ℝ) < t := fun n => hqt (n + N)
  have hq'mono : Monotone (fun n => (q' n : ℝ)) := by
    intro n m hnm
    change (q (n + N) : ℝ) ≤ (q (m + N) : ℝ)
    exact_mod_cast hqmono.monotone (Nat.add_le_add_right hnm N)
  have hq'tend : Tendsto (fun n => (q' n : ℝ)) atTop (𝓝 t) :=
    hqtend.comp (tendsto_add_atTop_nat N)
  have hseq : ∀ n, Bornology.IsBounded (A (q' n)) ∧
      IsSubharmonicBall (μ ω) (A (q' n)) z := by
    intro n
    exact ⟨(hA (q' n) (hqpos n)).1, (hA (q' n) (hqpos n)).2.1⟩
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
  filter_upwards [hall, hpoint] with x hx hpoint
  constructor
  · intro hxB
    simp only [B, leftRationalMassEnvelope, mem_iUnion] at hxB
    obtain ⟨q, hq0, hqt, hmem⟩ := hxB
    exact hx q hq0 hqt hmem
  · intro hxt
    obtain ⟨n, hn⟩ := hpoint.exists
    have hxq : x ∈ A (q' n) := hn.mpr hxt
    simp only [B, leftRationalMassEnvelope, mem_iUnion]
    exact ⟨q' n, hqpos n, hqlt n, hxq⟩

end HarmonicBalls
