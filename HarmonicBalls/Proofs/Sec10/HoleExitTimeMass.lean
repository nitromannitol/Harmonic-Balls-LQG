import HarmonicBalls.Proofs.Sec10.HoleExitLowerSemicontinuity
import HarmonicBalls.Proofs.Sec10.HoleExtinctionTotalMass
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Mass of hole exit times

Mass conservation bounds the Liouville mass of points in a fixed initial
hole whose exit times fall in a later interval. The later closed cluster must
be compactly contained in the unit disc. No hole existence is asserted. -/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology
open scoped ENNReal

universe u

/-- Under I2 and Lemma 8.2, the mass of points in a bounded hole whose
exit times lie in an interval is at most the length of that interval, provided
its later closed cluster is compactly contained in the unit disc. -/
theorem ae_cluster_holeExitTime_interval_mass_le
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∀ a b : ℝ, t ≤ a → a < b →
      closure (cluster (μ ω) 1 z b) ⊆ ball 0 1 →
      μ ω {x | x ∈ U ∧ a < holeExitTime (fun s => closure (cluster (μ ω) 1 z s)) x ∧
        holeExitTime (fun s => closure (cluster (μ ω) 1 z s)) x < b} ≤ ENNReal.ofReal (b - a) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_times_bddAbove_ordConnected hI2
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    clusterOpenLaplacian_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterMonotone_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    clusterConservationOfMass_proved hI2 γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ,
    ae_measure_frontier_cluster_inter_ball_eq_zero_of_steps
      (clusterOpenLaplacian_proved hI2)
      (Section6.veryGoodAnnulusHarnackTypeStmt_of_volumeGrowth_only hI2) h82
      γ α₀ hγ hγ2 hα Ω P hC hcirc μ hGFF hμ] with ω htimes hopen hmono hmass hnull
  intro t ht z hz U hU hUb a b hta hab hclb
  have ha : 0 < a := ht.trans_le hta
  have hb : 0 < b := ha.trans hab
  let F : ℝ → Set ℂ := fun s => closure (cluster (μ ω) 1 z s)
  let τ : ℂ → ℝ := holeExitTime F
  let V : Set ℂ := {x | x ∈ U ∧ τ x < b}
  have hUs : U ⊆ (F t)ᶜ := by
    obtain ⟨p, hp, rfl⟩ := hU
    exact connectedComponentIn_subset _ _
  have hUdisc : U ⊆ ball (0 : ℂ) 1 :=
    bounded_complement_component_subset_unit_ball isClosed_closure
      (closure_minimal (cluster_subset_ball.trans ball_subset_closedBall) isClosed_closedBall) hU hUb
  have hVb : V ⊆ F b := by
    intro x hx
    by_contra hxb
    obtain ⟨p, hp, hpU⟩ := hU
    have hxcomponent : x ∈ connectedComponentIn (F t)ᶜ p := hpU.symm ▸ hx.1
    have heq : connectedComponentIn (F t)ᶜ x = U :=
      (connectedComponentIn_eq hxcomponent).symm.trans hpU
    have hbound : Bornology.IsBounded (connectedComponentIn (F t)ᶜ x) := heq ▸ hUb
    have hboundb := (bounded_complement_component_mono_at_point
      (closure_mono (hmono t b 1 ht (hta.trans hab.le) zero_lt_one z hz)) hxb hbound).2.2
    have hbs : b ∈ {s : ℝ | 0 < s ∧ x ∈ (F s)ᶜ ∧
        Bornology.IsBounded (connectedComponentIn (F s)ᶜ x)} := ⟨hb, hxb, hboundb⟩
    have hle : b ≤ τ x := le_csSup (htimes z hz x).2 hbs
    exact (not_le_of_gt hx.2) hle
  have hsubset : {x | x ∈ U ∧ a < τ x ∧ τ x < b} ⊆ V \ F a := by
    intro x hx
    refine ⟨⟨hx.1, hx.2.2⟩, ?_⟩
    have htx : x ∈ (F t)ᶜ := hUs hx.1
    obtain ⟨p, hp, hpU⟩ := hU
    have hxcomponent : x ∈ connectedComponentIn (F t)ᶜ p := hpU.symm ▸ hx.1
    have heq : connectedComponentIn (F t)ᶜ x = U :=
      (connectedComponentIn_eq hxcomponent).symm.trans hpU
    have htS : t ∈ {s : ℝ | 0 < s ∧ x ∈ (F s)ᶜ ∧
        Bornology.IsBounded (connectedComponentIn (F s)ᶜ x)} := ⟨ht, htx, heq ▸ hUb⟩
    obtain ⟨s, hs, has⟩ := exists_lt_of_lt_csSup ⟨t, htS⟩ hx.2.1
    intro hxa
    exact hs.2.1 (closure_mono (hmono a s 1 ha has.le zero_lt_one z hz) hxa)
  have hcla : F a ⊆ ball (0 : ℂ) 1 :=
    (closure_mono (hmono a b 1 ha hab.le zero_lt_one z hz)).trans hclb
  have hfront : μ ω (frontier (cluster (μ ω) 1 z a)) = 0 := by
    apply measure_mono_null _ (hnull a ha z hz)
    intro x hx
    exact ⟨hx, hcla (frontier_subset_closure hx)⟩
  have heq := (hmass 1 a zero_lt_one ha z hz).2.2 hcla hfront
  have hbound := measure_sdiff_cluster_closure_le_of_subset_later_closure (μ ω) ha.le hab.le
    (hopen a 1 ha zero_lt_one z hz).1 (hopen b 1 hb zero_lt_one z hz).1
    (hmono a b 1 ha hab.le zero_lt_one z hz) heq
    (hmass 1 b zero_lt_one hb z hz).1 (hnull b hb z hz) hVb
    (fun x hx => hUdisc hx.1)
  exact (measure_mono hsubset).trans hbound

/-- For each bounded hole, the pushforward of its restricted Liouville
measure by the spatial exit-time function obeys the same interval bound.
Measurability is pathwise; no joint measurability in the field is asserted. -/
theorem ae_cluster_holeExitTime_pushforward_interval_le
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h82 : TypicalPointManyGoodScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t → ∀ z ∈ ball (0 : ℂ) 1,
      ∀ U ∈ connectedComponentsIn (closure (cluster (μ ω) 1 z t))ᶜ,
      Bornology.IsBounded U → ∀ a b : ℝ, t ≤ a → a < b →
      closure (cluster (μ ω) 1 z b) ⊆ ball 0 1 →
      Measure.map (holeExitTime (fun s => closure (cluster (μ ω) 1 z s)))
        ((μ ω).restrict U) (Ioo a b) ≤ ENNReal.ofReal (b - a) := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_holeExitTime_interval_mass_le hI2 h82
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ,
    ae_lowerSemicontinuous_clusterHoleExitTime hI2
      γ hγ hγ2 α₀ hα Ω P hC hcirc μ hGFF hμ] with ω hbound hlsc
  intro t ht z hz U hU hUb a b hta hab hclb
  have hmeas := (hlsc z hz).measurable
  rw [Measure.map_apply hmeas measurableSet_Ioo,
    Measure.restrict_apply (hmeas measurableSet_Ioo)]
  convert hbound t ht z hz U hU hUb a b hta hab hclb using 1
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, mem_Ioo, mem_ofPred_eq]
  tauto

end HarmonicBalls
