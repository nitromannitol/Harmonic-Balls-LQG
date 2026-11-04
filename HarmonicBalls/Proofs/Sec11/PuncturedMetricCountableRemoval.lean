import HarmonicBalls.Proofs.Sec11.PuncturedMetricOriginExtension

/-! # Countable verification of puncture removal

The Section 8 inputs use Leonardo Bonanno's LatticeProb code. Equality of
punctured and unpunctured internal distances remains an explicit hypothesis.
-/

namespace HarmonicBalls

open MeasureTheory Filter Set Topology
open scoped ENNReal

/-- Every open set admits a countable dense subset that avoids the origin. -/
theorem exists_countable_dense_subset_sdiff_zero {V : Set ℂ} (hV : IsOpen V) :
    ∃ Q : Set ℂ, Q.Countable ∧ Q ⊆ V \ {0} ∧ V ⊆ closure Q := by
  obtain ⟨S, hcount, hdense⟩ := TopologicalSpace.exists_countable_dense ℂ
  let Q : Set ℂ := (S \ {0}) ∩ V
  refine ⟨Q, (hcount.mono sdiff_subset).mono inter_subset_left, ?_, ?_⟩
  · intro x hx
    exact ⟨hx.2, hx.1.2⟩
  · simpa only [Q, inter_comm] using (hdense.sdiff_singleton 0).open_subset_closure_inter hV

/-- Equality of punctured and unpunctured internal distances on a dense
subset extends to every pair of non-puncture points. -/
theorem IsEuclideanLengthMetric.internalMetric_sdiff_singleton_eq_of_dense
    {D : ℂ → ℂ → ℝ} (hD : IsEuclideanLengthMetric D)
    {V Q : Set ℂ} (hV : IsOpen V)
    (hdense : V ⊆ closure Q)
    (heq : ∀ x ∈ Q, ∀ y ∈ Q,
      internalMetric D (V \ {0}) x y = internalMetric D V x y) :
    ∀ x ∈ V \ {0}, ∀ y ∈ V \ {0},
      internalMetric D (V \ {0}) x y = internalMetric D V x y := by
  have hnonneg (x y : ℂ) : 0 ≤ D x y := by
    have ht := hD.triangle x y x
    rw [hD.self_eq_zero, hD.symm y x] at ht
    linarith
  intro x hx y hy
  obtain ⟨qx, hqx, hqxt⟩ := mem_closure_iff_seq_limit.mp (hdense hx.1)
  obtain ⟨qy, hqy, hqyt⟩ := mem_closure_iff_seq_limit.mp (hdense hy.1)
  have ht := hqxt.prodMk_nhds hqyt
  have hp := (hD.continuousAt_internalMetric_pair hnonneg
    (hV.sdiff isClosed_singleton) hx hy).tendsto.comp ht
  have hv := (hD.continuousAt_internalMetric_pair hnonneg hV hx.1 hy.1).tendsto.comp ht
  have he : (fun n => internalMetric D (V \ {0}) (qx n) (qy n)) =
      (fun n => internalMetric D V (qx n) (qy n)) :=
    funext fun n => heq _ (hqx n) _ (hqy n)
  change Tendsto (fun n => internalMetric D (V \ {0}) (qx n) (qy n)) atTop _ at hp
  change Tendsto (fun n => internalMetric D V (qx n) (qy n)) atTop _ at hv
  rw [he] at hp
  exact tendsto_nhds_unique hp hv

/-- It suffices to verify point removal almost surely for each pair in a
countable dense set; the exceptional event can be chosen uniformly in all
non-puncture endpoints. -/
theorem ae_internalMetric_sdiff_singleton_eq_of_countable_dense
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {D : Ω → ℂ → ℂ → ℝ}
    {V Q : Set ℂ} (hV : IsOpen V)
    (hdense : V ⊆ closure Q) (hcount : Q.Countable)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    (heq : ∀ x ∈ Q, ∀ y ∈ Q, ∀ᵐ ω ∂P,
      internalMetric (D ω) (V \ {0}) x y = internalMetric (D ω) V x y) :
    ∀ᵐ ω ∂P, ∀ x ∈ V \ {0}, ∀ y ∈ V \ {0},
      internalMetric (D ω) (V \ {0}) x y = internalMetric (D ω) V x y := by
  let : Countable Q := hcount.to_subtype
  have hall : ∀ᵐ ω ∂P, ∀ x : Q, ∀ y : Q,
      internalMetric (D ω) (V \ {0}) x y = internalMetric (D ω) V x y :=
    ae_all_iff.mpr fun x => ae_all_iff.mpr fun y => heq x x.2 y y.2
  filter_upwards [hmetric, hall] with ω hω heω
  apply hω.internalMetric_sdiff_singleton_eq_of_dense hV hdense
  intro x hx y hy
  exact heω ⟨x, hx⟩ ⟨y, hy⟩

/-- The normalized singular metric has a local representative on the whole
open set when point removal holds almost surely for each pair in one
countable dense set. -/
theorem IsWholePlaneGFF.exists_modConst_internal_singularMetric_of_countable_point_removal
    {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} {γ ξ α : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    {D : Ω → ℂ → ℂ → ℝ} (h : IsWholePlaneGFF P hC hcirc)
    (𝔇 : ((ℂ → ℝ) → ℝ) → ℂ → ℂ → ℝ) (h𝔇 : IsLQGMetric γ ξ 𝔇)
    (hD : ∀ᵐ ω ∂P, ∀ u v, 0 ≤ D ω u v ∧
      ENNReal.ofReal (D ω u v) =
        weylScaling (𝔇 (hC ω)) ξ (fun x => -α * Real.log ‖x‖) u v)
    (hmetric : ∀ᵐ ω ∂P, IsEuclideanLengthMetric (D ω))
    {U V Q : Set ℂ} (hV : IsOpen V) (hne : (V \ {0}).Nonempty) (hVU : V ⊆ U)
    (hdense : V ⊆ closure Q) (hcount : Q.Countable)
    (ψ : ℂ → ℝ) (hψ : IsTestFunction U ψ) (hψint : ∫ x, ψ x = 1)
    (hremove : ∀ x ∈ Q, ∀ y ∈ Q, ∀ᵐ ω ∂P,
      internalMetric (D ω) (V \ {0}) x y = internalMetric (D ω) V x y) :
    ∃ (c : Ω → ℝ) (G : Ω → ℂ → ℂ → ℝ≥0∞),
      (∀ᵐ ω ∂P, 0 < c ω) ∧
      (∀ x y, Measurable[Section6.fieldSigmaAlgebraModConst α hC U] (fun ω => G ω x y)) ∧
      ∀ᵐ ω ∂P, ∀ x ∈ V, ∀ y ∈ V,
        internalMetric (fun x y => c ω * D ω x y) V x y = G ω x y := by
  apply h.exists_modConst_internal_singularMetric_of_point_removal
    𝔇 h𝔇 hD hmetric hV hne hVU ψ hψ hψint
  exact ae_internalMetric_sdiff_singleton_eq_of_countable_dense hV hdense hcount hmetric hremove

#print axioms exists_countable_dense_subset_sdiff_zero
#print axioms IsEuclideanLengthMetric.internalMetric_sdiff_singleton_eq_of_dense
#print axioms ae_internalMetric_sdiff_singleton_eq_of_countable_dense
#print axioms IsWholePlaneGFF.exists_modConst_internal_singularMetric_of_countable_point_removal

end HarmonicBalls
