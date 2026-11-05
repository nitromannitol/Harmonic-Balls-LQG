import HarmonicBalls.Proofs.Sec10.HoleExitFrontierAtoms
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! # Domination of hole exit-time laws

A measure bounded by interval length on half-open intervals is bounded by
Lebesgue measure. This supplies a route from cluster mass increments to
absolute continuity of exit-time laws. -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

/-- An interval-length upper bound for a measure on the real line implies
its domination by Lebesgue measure. -/
theorem measure_le_volume_of_Ioc_le (ν : Measure ℝ)
    (h : ∀ a b : ℝ, ν (Ioc a b) ≤ ENNReal.ofReal (b - a)) : ν ≤ volume := by
  apply Measure.toOuterMeasure_le.mp
  have hv : (volume : Measure ℝ).toOuterMeasure = StieltjesFunction.id.outer := by
    rw [Real.volume_eq_stieltjes_id, StieltjesFunction.measure]
  rw [hv, StieltjesFunction.outer, OuterMeasure.le_ofFunction]
  intro S
  rw [StieltjesFunction.length_eq]
  apply le_iInf
  intro a
  apply le_iInf
  intro b
  apply le_iInf
  intro hS
  have hS' : S ⊆ Ioc a b := by
    intro x hx
    exact hS ⟨hx, notMem_botSet_of_lt (sub_lt_self x zero_lt_one)⟩
  exact (measure_mono hS').trans (h a b)

/-- If open-interval masses are bounded by length on a window and the measure
has no atoms, its restriction to that window is dominated by Lebesgue measure. -/
theorem restrict_Ioo_le_volume_of_interval_le (ν : Measure ℝ) [NullSingletonClass ν]
    {t T : ℝ}
    (h : ∀ a b : ℝ, t ≤ a → a < b → b ≤ T →
      ν (Ioo a b) ≤ ENNReal.ofReal (b - a)) :
    ν.restrict (Ioo t T) ≤ volume := by
  apply measure_le_volume_of_Ioc_le
  intro a b
  rw [Measure.restrict_apply measurableSet_Ioc]
  let p := max a t
  let q := min b T
  by_cases hpq : p < q
  · have hsub : Ioc a b ∩ Ioo t T ⊆ Ioo p q ∪ {b} := by
      intro x hx
      have hpx : p < x := max_lt hx.1.1 hx.2.1
      have hxq : x ≤ q := le_min hx.1.2 hx.2.2.le
      rcases lt_or_eq_of_le hxq with hxq | hxq
      · exact Or.inl ⟨hpx, hxq⟩
      · right
        have : x = b := by
            rcases le_total b T with hbt | htb
            · simpa [q, min_eq_left hbt] using hxq
            · have hq : q = T := min_eq_right htb
              linarith [hx.2.2]
        simpa using this
    calc
      ν (Ioc a b ∩ Ioo t T) ≤ ν (Ioo p q ∪ {b}) := measure_mono hsub
      _ ≤ ν (Ioo p q) + ν {b} := measure_union_le _ _
      _ = ν (Ioo p q) := by rw [measure_singleton, add_zero]
      _ ≤ ENNReal.ofReal (q - p) := h p q (le_max_right a t) hpq (min_le_right b T)
      _ ≤ ENNReal.ofReal (b - a) := ENNReal.ofReal_le_ofReal (by
        dsimp [p, q]; linarith [le_max_left a t, min_le_left b T])
  · have hempty : Ioc a b ∩ Ioo t T = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      have hpx : p < x := max_lt hx.1.1 hx.2.1
      have hxq : x ≤ q := le_min hx.1.2 hx.2.2.le
      exact hpq (hpx.trans_le hxq)
    rw [hempty, measure_empty]
    exact zero_le

universe u

/-- On any interval ending before compact containment fails, the pathwise
exit-time distribution of a bounded initial hole is dominated by Lebesgue
measure. The result does not assert that such a hole exists. -/
theorem ae_cluster_holeExitTime_pushforward_restrict_le_volume
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h61 : HarnackTypeEstimateStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∀ T : ℝ, t < T →
      closure (cluster (μ ω) 1 z T) ⊆ ball 0 1 →
      (Measure.map (holeExitTime (fun s => closure (cluster (μ ω) 1 z s)))
        ((μ ω).restrict U)).restrict (Ioo t T) ≤ volume := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_holeExitTime_pushforward_noAtoms_of_frontier hI2 hvolume h61 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_cluster_holeExitTime_pushforward_interval_le hI2 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ]
      with ω hno hinterval hmono
  intro t ht z hz U hU hUb T htT hclT
  let ν := Measure.map (holeExitTime (fun s => closure (cluster (μ ω) 1 z s))) ((μ ω).restrict U)
  have : NullSingletonClass ν := hno t ht z hz U hU hUb
  apply restrict_Ioo_le_volume_of_interval_le ν
  intro a b hta hab hbT
  have hb : 0 < b := ht.trans_le (hta.trans hab.le)
  have hclb : closure (cluster (μ ω) 1 z b) ⊆ ball 0 1 :=
    (closure_mono (hmono b T 1 hb hbT zero_lt_one z hz)).trans hclT
  exact hinterval t ht z hz U hU hUb a b hta hab hclb

end HarmonicBalls
