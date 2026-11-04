import HarmonicBalls.Proofs.Sec10.HolePointTimeInterval
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Measurability of the set of hole times

A countable dense set detects every open complementary component. Since each
point's hole times form an interval, the set of all hole times is open up to
countably many endpoints. No hole existence or absence is assumed.
-/

namespace HarmonicBalls

open Set Metric MeasureTheory Filter Topology

/-- If each point's positive hole times form an interval, then all positive
hole times are an open set together with at most countably many times. -/
theorem hole_times_open_modulo_countable
    (F : ℝ → Set ℂ) (hclosed : ∀ t, 0 < t → IsClosed (F t))
    (hinterval : ∀ x : ℂ, {t : ℝ | 0 < t ∧ x ∈ (F t)ᶜ ∧
      Bornology.IsBounded (connectedComponentIn (F t)ᶜ x)}.OrdConnected) :
    ∃ O : Set ℝ, IsOpen O ∧
      O ⊆ {t : ℝ | 0 < t ∧ ∃ U ∈ connectedComponentsIn (F t)ᶜ,
        Bornology.IsBounded U} ∧
      ({t : ℝ | 0 < t ∧ ∃ U ∈ connectedComponentsIn (F t)ᶜ,
        Bornology.IsBounded U} \ O).Countable := by
  obtain ⟨D, hDcount, hDdense⟩ := TopologicalSpace.exists_countable_dense ℂ
  let : Countable D := hDcount.to_subtype
  let S : D → Set ℝ := fun x => {t | 0 < t ∧ (x : ℂ) ∈ (F t)ᶜ ∧
    Bornology.IsBounded (connectedComponentIn (F t)ᶜ x)}
  let H : Set ℝ := {t | 0 < t ∧ ∃ U ∈ connectedComponentsIn (F t)ᶜ,
    Bornology.IsBounded U}
  have hH : H = ⋃ x : D, S x := by
    ext t
    constructor
    · rintro ⟨ht, U, hU, hbounded⟩
      obtain ⟨p, hp, hpU⟩ := hU
      have hUopen : IsOpen U := by
        rw [← hpU]
        exact (hclosed t ht).isOpen_compl.connectedComponentIn
      have hUne : U.Nonempty := ⟨p, hpU ▸ mem_connectedComponentIn hp⟩
      obtain ⟨x, hxU, hxD⟩ := hDdense.inter_open_nonempty U hUopen hUne
      have heq : connectedComponentIn (F t)ᶜ x = U := by
        rw [← hpU] at hxU ⊢
        exact (connectedComponentIn_eq hxU).symm
      have hxout : x ∈ (F t)ᶜ := by
        rw [← hpU] at hxU
        exact connectedComponentIn_subset _ _ hxU
      exact mem_iUnion.mpr ⟨⟨x, hxD⟩, ht, hxout, heq ▸ hbounded⟩
    · intro ht
      obtain ⟨x, htpos, hx, hb⟩ := mem_iUnion.mp ht
      exact ⟨htpos, _, ⟨x, hx, rfl⟩, hb⟩
  let O : Set ℝ := ⋃ x : D, interior (S x)
  have hOopen : IsOpen O := isOpen_iUnion fun _ => isOpen_interior
  have hOsub : O ⊆ H := by
    rw [hH]
    exact iUnion_mono fun _ => interior_subset
  have hfinite (x : D) : (S x \ interior (S x)).Finite := by
    apply (S x).finite_sdiff_iUnion_Ioo.subset
    intro t ht
    refine ⟨ht.1, ?_⟩
    intro hmem
    apply ht.2
    apply mem_interior_iff_mem_nhds.mpr
    obtain ⟨a, ha, b, hb, hab⟩ := by simpa only [mem_iUnion] using hmem
    exact mem_of_superset (isOpen_Ioo.mem_nhds hab)
      (Ioo_subset_Icc_self.trans ((hinterval x).out ha hb))
  refine ⟨O, hOopen, hOsub, ?_⟩
  change (H \ O).Countable
  rw [hH]
  apply (countable_iUnion fun x : D => (hfinite x).countable).mono
  intro t ht
  obtain ⟨x, hx⟩ := mem_iUnion.mp ht.1
  exact mem_iUnion.mpr ⟨x, hx, fun h => ht.2 (mem_iUnion.mpr ⟨x, h⟩)⟩

universe u

/-- Under I2, simultaneously for every pole, positive times with a bounded
complementary component are open modulo a countable set and hence Borel. -/
theorem ae_cluster_hole_times_open_modulo_countable
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      let H := {t : ℝ | 0 < t ∧ ∃ U ∈ connectedComponentsIn
        (closure (cluster (μ ω) 1 z t))ᶜ, Bornology.IsBounded U}
      (∃ O : Set ℝ, IsOpen O ∧ O ⊆ H ∧ (H \ O).Countable) ∧ MeasurableSet H := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_times_ordConnected hI2 γ hγ hγ2 α₀ hα
    Ω P hC hcirc μ hGFF hμ] with ω hinterval
  intro z hz
  obtain ⟨O, hOopen, hOsub, hcount⟩ := hole_times_open_modulo_countable
    (fun t => closure (cluster (μ ω) 1 z t)) (fun _ _ => isClosed_closure)
    (hinterval z hz)
  refine ⟨⟨O, hOopen, hOsub, hcount⟩, ?_⟩
  rw [← union_sdiff_cancel hOsub]
  exact hOopen.measurableSet.union hcount.measurableSet

/-- Under I2, for every pole, either hole times are countable or they contain
an interval of positive length. This does not assert that either case occurs. -/
theorem ae_cluster_hole_times_countable_or_contains_interval
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      let H := {t : ℝ | 0 < t ∧ ∃ U ∈ connectedComponentsIn
        (closure (cluster (μ ω) 1 z t))ᶜ, Bornology.IsBounded U}
      H.Countable ∨ ∃ a b : ℝ, a < b ∧ Ioo a b ⊆ H := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_times_open_modulo_countable hI2 γ hγ hγ2 α₀ hα
    Ω P hC hcirc μ hGFF hμ] with ω hω
  intro z hz
  obtain ⟨⟨O, hOopen, hOsub, hcount⟩, _⟩ := hω z hz
  by_cases hne : O.Nonempty
  · right
    obtain ⟨a, b, hab, hsub⟩ := hOopen.exists_Ioo_subset hne
    exact ⟨a, b, hab, hsub.trans hOsub⟩
  · left
    have hempty : O = ∅ := not_nonempty_iff_eq_empty.mp hne
    simpa only [hempty, sdiff_empty] using hcount

/-- Under I2, for every pole, almost-everywhere absence of holes in time is
equivalent to having only countably many hole times. -/
theorem ae_cluster_hole_times_countable_iff_volume_zero
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) :
    ∀ γ : ℝ, 0 < γ → γ < 2 → ∀ α₀ : ℝ, α₀ < lqgQ γ →
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
      (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ),
    IsWholePlaneGFF P hC hcirc → IsLQGMeasureOfField P γ α₀ hcirc μ →
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1,
      let H := {t : ℝ | 0 < t ∧ ∃ U ∈ connectedComponentsIn
        (closure (cluster (μ ω) 1 z t))ᶜ, Bornology.IsBounded U}
      H.Countable ↔ volume H = 0 := by
  intro γ hγ hγ2 α₀ hα Ω _ P hC hcirc μ hGFF hμ
  filter_upwards [ae_cluster_hole_times_open_modulo_countable hI2 γ hγ hγ2 α₀ hα
    Ω P hC hcirc μ hGFF hμ] with ω hω
  intro z hz
  obtain ⟨⟨O, hOopen, hOsub, hcount⟩, _⟩ := hω z hz
  constructor
  · intro h
    exact h.measure_zero volume
  · intro hzero
    have hempty : O = ∅ := by
      apply not_nonempty_iff_eq_empty.mp
      intro hne
      have hpos : 0 < volume O := hOopen.measure_pos volume hne
      exact (ne_of_gt hpos) (measure_mono_null hOsub hzero)
    simpa only [hempty, sdiff_empty] using hcount

end HarmonicBalls
