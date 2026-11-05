import HarmonicBalls.Proofs.Sec6.RelativeDenseGoodAnnulusCounts
import HarmonicBalls.Proofs.Sec6.CountableNearbyAnnulusIteration

/-! # Scaled dense families of nearby annulus centres -/

namespace HarmonicBalls.Section6

open MeasureTheory Metric Set Filter Topology
open scoped ENNReal

private instance : Nonempty (ball (0 : ℂ) ((1 : ℝ) / 100)) :=
  ⟨⟨0, mem_ball_self (by norm_num)⟩⟩

/-- A deterministic countable family dense in the relative centre ball. -/
noncomputable def nearbyDenseCentre (i : ℕ) : ℂ :=
  (TopologicalSpace.denseSeq (ball (0 : ℂ) ((1 : ℝ) / 100)) i).val

theorem nearbyDenseCentre_mem (i : ℕ) :
    nearbyDenseCentre i ∈ ball (0 : ℂ) ((1 : ℝ) / 100) :=
  (TopologicalSpace.denseSeq (ball (0 : ℂ) ((1 : ℝ) / 100)) i).property

/-- Every point obtained by scaling and translating the relative ball is in
 the closure of the correspondingly scaled and translated centre family. -/
theorem mem_closure_range_scaled_nearbyDenseCentre (x : ℂ) (t : ℝ)
    {v : ℂ} (hv : v ∈ ball (0 : ℂ) ((1 : ℝ) / 100)) :
    x + t • v ∈ closure (range (fun i => x + t • nearbyDenseCentre i)) := by
  let v' : ball (0 : ℂ) ((1 : ℝ) / 100) := ⟨v, hv⟩
  let f : ball (0 : ℂ) ((1 : ℝ) / 100) → ℂ := fun w => x + t • w.val
  have hf : Continuous f := continuous_const.add ((continuous_const_smul t).comp continuous_subtype_val)
  have hd : v' ∈ closure (range (TopologicalSpace.denseSeq
      (ball (0 : ℂ) ((1 : ℝ) / 100)))) := (TopologicalSpace.denseRange_denseSeq _) v'
  have h := mem_closure_image hf.continuousAt hd
  simpa only [f, v', ← Set.range_comp', nearbyDenseCentre] using h

/-- The count at all scaled nearby centres is bounded by the relaxed count
at mass-typical roots lying in every scaled relative centre ball. -/
theorem ae_scaled_nearby_goodAnnuli_count_le_root_count
    (μ : Measure ℂ) [IsLocallyFiniteMeasure μ] [NullSingletonClass μ] :
    ∀ᵐ z ∂μ, ∀ (S : Set ℝ), S.Finite → ∀ (x : ℂ) (R : ℝ → ℝ),
      ∀ {a a' b b' : ℝ}, 0 ≤ a' → a' < a → 0 ≤ b → b < b' →
      (∀ r ∈ S, 0 < R r ∧
        (∃ v ∈ ball (0 : ℂ) ((1 : ℝ) / 100), z = x + R r • v) ∧
        0 < μ (annulus z (3 * R r) (5 * R r))) →
      {r ∈ S | ∀ i, IsGoodAnnulus μ (R r) (x + R r • nearbyDenseCentre i) a b}.ncard ≤
        {r ∈ S | IsGoodAnnulus μ (R r) z a' b'}.ncard := by
  filter_upwards [ae_relative_dense_goodAnnuli_count_le_root_count μ] with z hz
  intro S hS x R a a' b b' ha' ha hb hbb hreg
  apply hz S hS R (fun r i => x + R r • nearbyDenseCentre i) ha' ha hb hbb
  intro r hr
  obtain ⟨hrpos, ⟨v, hv, hvz⟩, hp⟩ := hreg r hr
  exact ⟨hrpos, hvz ▸ mem_closure_range_scaled_nearbyDenseCentre x (R r) hv, hp⟩

universe u

/-- The scaled-family comparison holds for LQG-mass-typical roots under
 the all-scales volume-growth input. -/
theorem ae_lqg_ae_scaled_nearby_goodAnnuli_count_le_root_count
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    {γ α₀ : ℝ} (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ᵐ z ∂(μ ω), ∀ (S : Set ℝ), S.Finite → ∀ (x : ℂ) (R : ℝ → ℝ),
      ∀ {a a' b b' : ℝ}, 0 ≤ a' → a' < a → 0 ≤ b → b < b' →
      (∀ r ∈ S, 0 < R r ∧
        (∃ v ∈ ball (0 : ℂ) ((1 : ℝ) / 100), z = x + R r • v) ∧
        0 < μ ω (annulus z (3 * R r) (5 * R r))) →
      {r ∈ S | ∀ i, IsGoodAnnulus (μ ω) (R r)
        (x + R r • nearbyDenseCentre i) a b}.ncard ≤
        {r ∈ S | IsGoodAnnulus (μ ω) (R r) z a' b'}.ncard := by
  filter_upwards [ae_lqg_ae_relative_dense_goodAnnuli_count_le_root_count
    hI2 hγ hγ2 hα hGFF hμ] with ω hω
  filter_upwards [hω] with z hz
  intro S hS x R a a' b b' ha' ha hb hbb hreg
  apply hz S hS R (fun r i => x + R r • nearbyDenseCentre i) ha' ha hb hbb
  intro r hr
  obtain ⟨hrpos, ⟨v, hv, hvz⟩, hp⟩ := hreg r hr
  exact ⟨hrpos, hvz ▸ mem_closure_range_scaled_nearbyDenseCentre x (R r) hv, hp⟩

/-- The count of radii good at all centres of the scaled dense family has
 the polynomial lower-tail bound from the countable-centre estimate. -/
theorem exists_scaled_dense_goodAnnuli_count_tail
    (hgrowth : LQGVolumeGrowthAllScalesStmt.{u})
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ : ℝ}
    (hγ : 0 < γ) (hγ2 : γ < 2)
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (h : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ 0 hcirc μ)
    {b : ℝ} (hb : 0 < b) (α β : ℝ) (hα : 0 < α) (hβ : β ∈ Ioo (0 : ℝ) 1) :
    ∃ a ∈ Ioo (0 : ℝ) 1, ∃ C : ℝ, 0 < C ∧
    ∀ (x : ℂ) (s : ℝ), 0 < s → ∀ ε : ℝ, 0 < ε →
      16 ≤ Real.logb 7 (ε ^ (-1 : ℝ)) →
      P {ω | ({r : ℝ | r ∈ Icc ε (ε ^ (3 / 4 : ℝ)) ∧
        (∃ n : ℕ, r = (7 : ℝ)⁻¹ ^ n) ∧
        ∀ i, IsGoodAnnulus (μ ω) (s * r)
          (x + (s * r) • nearbyDenseCentre i) a b}.ncard : ℝ) <
        (β / 16) * Real.logb 7 (ε ^ (-1 : ℝ))} ≤
      ENNReal.ofReal (C * ε ^ (α / (16 * Real.log 7))) := by
  obtain ⟨a, ha, C, hC, ht⟩ :=
    exists_countable_nearby_goodAnnuli_count_tail_all_centres hgrowth hγ hγ2 h hμ hb α β hα hβ
  exact ⟨a, ha, C, hC, fun x s hs ε hε hlog =>
    ht x nearbyDenseCentre nearbyDenseCentre_mem s hs ε hε hlog⟩

end HarmonicBalls.Section6
