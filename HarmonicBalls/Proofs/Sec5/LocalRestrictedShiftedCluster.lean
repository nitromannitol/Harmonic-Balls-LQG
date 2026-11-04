import HarmonicBalls.Proofs.Sec5.LocalRestrictedPotential

/-! # Field-local shifted obstacle clusters for restricted measures

Continuity of the Green potential and nonemptiness of shifted supersolutions
suffice to decode the shifted odometer from the potential. Both conditions
hold for a restriction of a locally finite measure satisfying volume growth.
-/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter TopologicalSpace

/-- A continuous decoder works for any measure with continuous potential and
a nonempty shifted supersolution class, with no lower volume-growth condition. -/
theorem exists_continuous_shiftedOdometer_decoder_of_nonempty
    {R t : ℝ} {z x : ℂ} (hR : 0 < R)
    (hx : x ∈ closedBall (0 : ℂ) R) (hxz : x ≠ z) :
    ∃ g : C(closedBall (0 : ℂ) R, ℝ) → ℝ, Continuous g ∧
      ∀ ν : Measure ℂ, ContinuousOn (greenPotentialBall ν R) (closedBall 0 R) →
        (shiftedSupersolutions ν R z t).Nonempty →
        ∀ q : C(closedBall (0 : ℂ) R, ℝ),
          (∀ y, q y = greenPotentialBall ν R y) → shiftedOdometer ν R z t x = g q := by
  classical
  let A := {ν : Measure ℂ // ContinuousOn (greenPotentialBall ν R) (closedBall 0 R) ∧
    (shiftedSupersolutions ν R z t).Nonempty}
  obtain ⟨Q, _, hQeq⟩ := exists_measurable_greenPotentialBall_decoder hR
  let q : A → C(closedBall (0 : ℂ) R, ℝ) := fun a => Q a.1
  let f : A → ℝ := fun a => shiftedOdometer a.1 R z t x
  have hdist : ∀ a b, dist (f a) (f b) ≤ (2 : NNReal) * dist (q a) (q b) := by
    intro a b
    rw [Real.dist_eq]
    apply abs_shiftedOdometer_sub_le_of_greenPotentialBall a.2.2 b.2.2 ?_ hx hxz
    intro y hy
    have h := ContinuousMap.dist_apply_le_dist (f := q a) (g := q b) ⟨y, hy⟩
    simpa only [Real.dist_eq, q, hQeq _ a.2.1, hQeq _ b.2.1] using h
  obtain ⟨g, hg, hgf⟩ := exists_lipschitz_factor_of_dist_le q f 2 hdist
  refine ⟨g, hg.continuous, ?_⟩
  intro ν hν hclass q' hq'
  let a : A := ⟨ν, hν, hclass⟩
  have hqeq : q' = q a := by
    ext y
    rw [hq' y, hQeq _ hν]
  rw [hqeq]
  exact hgf a

/-- The shifted supersolution class of a dominated measure is nonempty at
nonnegative times, without any lower mass bound for that measure. -/
theorem shiftedSupersolutions_nonempty_of_dominated
    {μ σ : Measure ℂ} (hμ : IsLocallyFiniteMeasure μ)
    {R βm βp : ℝ} (hR : 0 < R) (hV : VolumeGrowth μ R βm βp) (hσ : σ ≤ μ)
    {z : ℂ} {t : ℝ} (ht : 0 ≤ t) : (shiftedSupersolutions σ R z t).Nonempty := by
  have hqeq : greenPotentialBall (σ.restrict (ball 0 R)) R = greenPotentialBall σ R := by
    funext x
    unfold greenPotentialBall
    rw [Measure.restrict_restrict measurableSet_ball, inter_self]
  obtain ⟨hqc, hΔ⟩ := dominated_greenPotentialBall hμ hR hV hσ
  rw [hqeq] at hqc hΔ
  exact ⟨greenPotentialBall σ R, greenPotentialBall_mem_shiftedSupersolutions ht hqc hΔ.laplacianLE⟩

universe u

/-- The shifted non-coincidence sets of a restricted LQG measure have a
field-local representative, simultaneously for all centres and positive times.
No comparison with the unshifted cluster is asserted here. -/
theorem exists_local_lqg_restricted_nonCoincidenceFamily_representative
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) {R : ℝ} (hR : 0 < R) :
    ∃ F : Ω → (ball (0 : ℂ) R × Ioi (0 : ℝ) → Set ℂ),
      Measurable[fieldSigmaAlgebra α₀ hC U] F ∧
      ∀ᵐ ω ∂P, F ω = fun p => nonCoincidenceSet ((μ ω).restrict U) R p.1 p.2 := by
  classical
  obtain ⟨βm, βp, hae⟩ := ae_isLocallyFiniteMeasure_volumeGrowth hI2 hγ hγ2 hα hGFF hμ
  obtain ⟨Q, hQ, hQeq⟩ := exists_local_lqg_restricted_greenPotentialBall_continuous_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hU hR
  let J := ball (0 : ℂ) R × Ioi (0 : ℝ)
  let G : J → ℂ → C(closedBall (0 : ℂ) R, ℝ) → ℝ := fun p x =>
    if h : x ∈ ball (0 : ℂ) R ∧ x ≠ p.1 then
      Classical.choose (exists_continuous_shiftedOdometer_decoder_of_nonempty (t := p.2) hR
        (ball_subset_closedBall h.1) h.2)
    else fun _ => 0
  have hG : ∀ p x, Continuous (G p x) := by
    intro p x
    dsimp only [G]
    split_ifs with h
    · exact (Classical.choose_spec
        (exists_continuous_shiftedOdometer_decoder_of_nonempty (t := p.2) hR
          (ball_subset_closedBall h.1) h.2)).1
    · exact continuous_const
  let F : Ω → J → Set ℂ := fun ω p =>
    {x | x ∈ ball (0 : ℂ) R ∧ (x = p.1 ∨ 0 < G p x (Q ω))}
  have hF : Measurable[fieldSigmaAlgebra α₀ hC U] F := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    apply Measurable.of_eval
    intro p
    apply Measurable.of_eval
    intro x
    exact measurable_const.and (measurable_const.or (measurable_const.lt ((hG p x).measurable.comp hQ)))
  refine ⟨F, hF, ?_⟩
  filter_upwards [hae, hQeq] with ω hω hqω
  funext p
  ext x
  by_cases hx : x ∈ ball (0 : ℂ) R
  · by_cases hxz : x = p.1
    · change (x ∈ ball (0 : ℂ) R ∧ (x = p.1 ∨ 0 < G p x (Q ω))) ↔ _
      rw [mem_nonCoincidenceSet_iff]
      simp only [hxz, true_or]
    · have hgood := (Classical.choose_spec
        (exists_continuous_shiftedOdometer_decoder_of_nonempty (t := p.2) hR
          (ball_subset_closedBall hx) hxz)).2
      have hgeq : shiftedOdometer ((μ ω).restrict U) R p.1 p.2 x = G p x (Q ω) := by
        have hp : x ∈ ball (0 : ℂ) R ∧ x ≠ p.1 := ⟨hx, hxz⟩
        simpa only [G, dite_eq_left hp] using hgood ((μ ω).restrict U)
          (continuousOn_greenPotentialBall_restrict_of_volumeGrowth hω.1 hR (hω.2 R hR))
          (shiftedSupersolutions_nonempty_of_dominated hω.1 hR (hω.2 R hR)
            Measure.restrict_le_self p.2.property.le) (Q ω) hqω
      rw [mem_nonCoincidenceSet_iff]
      simp only [F, mem_ofPred_eq, hx, hxz, false_or, true_and, hgeq]
  · change (x ∈ ball (0 : ℂ) R ∧ (x = p.1 ∨ 0 < G p x (Q ω))) ↔ _
    rw [mem_nonCoincidenceSet_iff]
    simp only [hx, false_and]

end HarmonicBalls
