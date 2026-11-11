import HarmonicBalls.Proofs.Sec5.InteriorHausdorffContinuity
import HarmonicBalls.Proofs.Sec5.BoundaryJumpCount
import HarmonicBalls.Proofs.Sec5.BoundaryContinuityCompactness

/-! # Right continuity and boundary-contact length

The scalar criterion below does not establish its own continuity hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter Topology Section6
open scoped Pointwise ENNReal MeasureTheory

/-- For an increasing family, convergence of dyadic boundary-contact lengths
is equivalent to the absence of a positive-length boundary jump. -/
theorem tendsto_boundary_contact_length_iff_null_jump
    (F : ℝ → Set ℂ) {t : ℝ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s') :
    Tendsto (fun n : ℕ => μH[1] (closure (F (t + dyadicScale n)) ∩ sphere 0 1))
      atTop (𝓝 (μH[1] (closure (F t) ∩ sphere 0 1))) ↔
    μH[1] (((⋂ n : ℕ, closure (F (t + dyadicScale n))) ∩ sphere 0 1) \
      closure (F t)) = 0 := by
  let A : ℕ → Set ℂ := fun n => closure (F (t + dyadicScale n)) ∩ sphere 0 1
  let B : Set ℂ := closure (F t) ∩ sphere 0 1
  have ha : Antitone A := by
    intro i j hij
    apply inter_subset_inter_left _
    apply closure_mono
    apply hmono _ _ (add_pos ht (dyadicScale_pos j))
    dsimp [dyadicScale]
    exact add_le_add le_rfl (pow_le_pow_of_le_one (by norm_num) (by norm_num) hij)
  have hm : ∀ n, NullMeasurableSet (A n) μH[1] :=
    fun _ => (isClosed_closure.inter isClosed_sphere).measurableSet.nullMeasurableSet
  have hf : μH[1] (sphere (0 : ℂ) 1) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hausdorffMeasure_one_unit_sphere_le
  have ha_fin : μH[1] (A 0) ≠ ⊤ := ne_top_of_le_ne_top hf (measure_mono inter_subset_right)
  have hb_fin : μH[1] B ≠ ⊤ := ne_top_of_le_ne_top hf (measure_mono inter_subset_right)
  have hb : B ⊆ ⋂ n, A n := by
    intro x hx
    apply mem_iInter.mpr
    intro n
    exact ⟨closure_mono (hmono t _ ht (le_add_of_nonneg_right (dyadicScale_pos n).le)) hx.1, hx.2⟩
  have hlim := tendsto_measure_iInter_atTop hm ha ⟨0, ha_fin⟩
  have heq : (⋂ n, A n) = (⋂ n, closure (F (t + dyadicScale n))) ∩ sphere 0 1 := by
    ext x
    simp only [A, mem_iInter, mem_inter_iff]
    constructor
    · intro h; exact ⟨fun n => (h n).1, (h 0).2⟩
    · rintro ⟨h, hs⟩ n; exact ⟨h n, hs⟩
  have hdiff : (⋂ n, A n) \ B =
      ((⋂ n, closure (F (t + dyadicScale n))) ∩ sphere 0 1) \ closure (F t) := by
    rw [heq]
    ext x
    simp only [B, Set.mem_sdiff, mem_inter_iff]
    tauto
  constructor
  · intro h
    have hmeas : μH[1] (⋂ n, A n) = μH[1] B := tendsto_nhds_unique hlim h
    rw [← hdiff, measure_sdiff hb (isClosed_closure.inter isClosed_sphere).measurableSet.nullMeasurableSet hb_fin,
      hmeas, tsub_self]
  · intro hnull
    have hmeas : μH[1] B = μH[1] (⋂ n, A n) :=
      measure_eq_measure_of_null_sdiff hb (by rwa [hdiff])
    change Tendsto (μH[1] ∘ A) atTop (𝓝 (μH[1] B))
    rwa [hmeas]

/-- For a monotone family, the dyadic contact-length limit is equivalent to
one-sided continuity of the contact length. -/
theorem tendsto_boundary_contact_length_dyadic_iff
    (F : ℝ → Set ℂ) {t : ℝ} (ht : 0 < t)
    (hmono : ∀ s s', 0 < s → s ≤ s' → F s ⊆ F s') :
    Tendsto (fun n : ℕ => μH[1] (closure (F (t + dyadicScale n)) ∩ sphere 0 1))
        atTop (𝓝 (μH[1] (closure (F t) ∩ sphere 0 1))) ↔
      Tendsto (fun s : ℝ => μH[1] (closure (F s) ∩ sphere 0 1))
        (𝓝[≥] t) (𝓝 (μH[1] (closure (F t) ∩ sphere 0 1))) := by
  constructor
  · intro hseq
    apply tendsto_order.mpr
    constructor
    · intro a ha
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact lt_of_lt_of_le ha (measure_mono (inter_subset_inter_left _
        (closure_mono (hmono t s ht hs))))
    · intro a ha
      obtain ⟨n, hn⟩ := (hseq.eventually (Iio_mem_nhds ha)).exists
      filter_upwards [self_mem_nhdsWithin,
        eventually_nhdsWithin_of_eventually_nhds
          (Iio_mem_nhds (lt_add_of_pos_right t (dyadicScale_pos n)))] with s hs hsupper
      exact lt_of_le_of_lt (measure_mono (inter_subset_inter_left _
        (closure_mono (hmono s (t + dyadicScale n) (ht.trans_le hs) hsupper.le)))) hn
  · intro hright
    have htime : Tendsto (fun n : ℕ => t + dyadicScale n) atTop (𝓝[≥] t) := by
      apply tendsto_nhdsWithin_iff.mpr
      constructor
      · simpa using (tendsto_const_nhds.add
          (tendsto_dyadicScale_nhdsGT.mono_right nhdsWithin_le_nhds) :
          Tendsto (fun n : ℕ => t + dyadicScale n) atTop (𝓝 (t + 0)))
      · filter_upwards with n
        exact le_add_of_nonneg_right (dyadicScale_pos n).le
    exact hright.comp htime

universe u

/-- Almost surely, geometric right continuity at any positive time is
exactly right continuity of the one-dimensional length of the circle contact set. -/
theorem ae_cluster_right_continuity_iff_boundary_contact_length
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u}) (hvolume : LiouvilleVolumeGrowthStmt.{u})
    (h32 : ClusterOpenLaplacianStmt.{u}) (h33 : ClusterMonotoneStmt.{u})
    (h34 : ClusterConservationOfMassStmt.{u}) (h61 : HarnackTypeEstimateStmt.{u})
    (h611 : VeryGoodAnnulusHarnackTypeStmt.{u}) (h82 : TypicalPointManyGoodScalesStmt.{u})
    (γ α₀ : ℝ) (hγ : 0 < γ) (hγ2 : γ < 2) (hα₀ : α₀ < lqgQ γ)
    (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω)
    (hC : Ω → (ℂ → ℝ) → ℝ) (hcirc : Ω → ℝ → ℂ → ℝ) (μ : Ω → Measure ℂ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ) :
    ∀ᵐ ω ∂P, ∀ z ∈ ball (0 : ℂ) 1, ∀ t : ℝ, 0 < t →
      ((∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s ∈ Icc t (t + δ),
        closure (cluster (μ ω) 1 z s) ⊆ cluster (μ ω) 1 z t + ball (0 : ℂ) ε) ↔
      Tendsto (fun s : ℝ => μH[1]
        (closure (cluster (μ ω) 1 z s) ∩ sphere 0 1))
        (𝓝[≥] t) (𝓝 (μH[1] (closure (cluster (μ ω) 1 z t) ∩ sphere 0 1)))) := by
  filter_upwards [h33 γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ,
    ae_right_discontinuity_has_positive_new_circle_length hI2 hvolume h32 h33 h34 h61 h611 h82
      γ α₀ hγ hγ2 hα₀ Ω P hC hcirc μ hGFF hμ] with ω hmono hpositive
  intro z hz t ht
  have hm : ∀ s s', 0 < s → s ≤ s' → cluster (μ ω) 1 z s ⊆ cluster (μ ω) 1 z s' :=
    fun s s' hs hss' => hmono s s' 1 hs hss' zero_lt_one z hz
  rw [← tendsto_boundary_contact_length_dyadic_iff _ ht hm,
    tendsto_boundary_contact_length_iff_null_jump _ ht hm]
  constructor
  · intro hcont
    have hsub := (cluster_closure_dyadic_iInter_subset_iff_right_continuous ht hm).mpr hcont
    apply measure_mono_null _ (measure_empty : μH[1] (∅ : Set ℂ) = 0)
    intro x hx
    exact False.elim (hx.2 (hsub hx.1.1))
  · intro hnull
    by_contra hfail
    exact (ne_of_gt (hpositive z hz t ht hfail)) hnull


end HarmonicBalls
