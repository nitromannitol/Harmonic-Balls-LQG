import HarmonicBalls.Proofs.Sec8.CanonicalCircleDecoder
import HarmonicBalls.Proofs.Sec8.RawRootedApproximation

/-! # Rooted normalized approximations from the canonical field

The distribution reconstruction and imported Section 8 arguments use
Leonardo Bonanno's LatticeProb formalization.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Set Metric
open scoped ENNReal Topology

namespace HarmonicBalls

/-- Buffered translated LQG approximations are measurable functions of the
original canonical field and the root, simultaneously for every root in the
buffer and every dyadic scale. -/
theorem IsWholePlaneGFF.exists_canonical_rooted_normalizedLQGApprox
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ R : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (H : Ω → LQGMetric.DistC)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1))
    (B : Set ℂ) (E : ℕ → Set ℂ) (hEm : ∀ n, MeasurableSet (E n))
    (hbuffer : ∀ n z, z ∈ B →
      closedBall z (dyadicScale n) ⊆ ball 0 R ∧
      ∀ x ∈ E n, closedBall (x + z) (dyadicScale n) ⊆ ball 0 R) :
    ∃ F : ℕ → (LQGMetric.DistC × ℂ) → Measure ℂ,
      (∀ n, Measurable (F n)) ∧ ∀ᵐ ω ∂P, ∀ z ∈ B, ∀ n,
        F n (H ω, z) = normalizedRestriction
          (lqgApprox γ (fun r x => fieldCircleAverage α₀ (hcirc ω) r (x + z))
            (dyadicScale n)) (E n) := by
  obtain ⟨D, hDm, hDeq⟩ :=
    hh.exists_canonical_local_centeredCircle_decoders (α₀ := α₀) (ε := R) H hversion
  let L : LQGMetric.DistC → Section6.LocalTest (ball 0 R) → ℝ :=
    fun h φ => h φ.1.1
  have hLm : Measurable L := measurable_pi_iff.mpr fun φ =>
    LQGMetric.measurable_distOn_apply φ.1.1
  let d : ℕ → (LQGMetric.DistC × ℂ) → ℂ → ℝ :=
    fun n p x => D n (L p.1) (x + p.2) - D n (L p.1) p.2
  have hdm (n : ℕ) : Measurable (Function.uncurry (d n)) := by
    apply Measurable.sub
    · exact (hDm n).comp ((hLm.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.add (measurable_snd.comp measurable_fst)))
    · exact (hDm n).comp ((hLm.comp (measurable_fst.comp measurable_fst)).prodMk
        (measurable_snd.comp measurable_fst))
  refine ⟨fun n p => normalizedRestriction
    (volume.withDensity fun x => ENNReal.ofReal (Real.exp (γ * d n p x))) (E n), ?_, ?_⟩
  · exact fun n => measurable_normalized_centeredLQGApprox γ (d n) (hdm n) (E n) (hEm n)
  · filter_upwards [hDeq] with ω hω z hz n
    apply (normalizedRestriction_lqgApprox_eq_of_centered_on γ
      (fun r x => fieldCircleAverage α₀ (hcirc ω) r (x + z))
      (dyadicScale_pos n) 0 (hEm n) _ ?_).symm
    intro x hx
    have h₁ := hω n (x + z) ((hbuffer n z hz).2 x hx)
    have h₂ := hω n z ((hbuffer n z hz).1)
    change D n (fun φ => H ω φ.1.1) (x + z) -
      D n (fun φ => H ω φ.1.1) z = _
    rw [h₁, h₂]
    simp only [zero_add]
    ring

/-- The canonical rooted decoder applies under any sampling kernel which
chooses roots in the buffered set almost surely. -/
theorem IsWholePlaneGFF.exists_sampled_canonical_normalizedLQGApprox
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ R : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ}
    (hh : IsWholePlaneGFF P hC hcirc) (H : Ω → LQGMetric.DistC)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1))
    (κ : Kernel Ω ℂ) (B : Set ℂ)
    (hκ : ∀ᵐ p ∂P ⊗ₘ κ, p.2 ∈ B)
    (E : ℕ → Set ℂ) (hEm : ∀ n, MeasurableSet (E n))
    (hbuffer : ∀ n z, z ∈ B →
      closedBall z (dyadicScale n) ⊆ ball 0 R ∧
      ∀ x ∈ E n, closedBall (x + z) (dyadicScale n) ⊆ ball 0 R) :
    ∃ F : ℕ → (LQGMetric.DistC × ℂ) → Measure ℂ,
      (∀ n, Measurable (F n)) ∧ ∀ᵐ p ∂P ⊗ₘ κ, ∀ n,
        F n (H p.1, p.2) = normalizedRestriction
          (lqgApprox γ (fun r x => fieldCircleAverage α₀ (hcirc p.1) r (x + p.2))
            (dyadicScale n)) (E n) := by
  obtain ⟨F, hFm, hFeq⟩ := hh.exists_canonical_rooted_normalizedLQGApprox
    (γ := γ) (α₀ := α₀) H hversion B E hEm hbuffer
  refine ⟨F, hFm, ?_⟩
  filter_upwards [ae_fst_of_ae_compProd P κ hFeq, hκ] with p hp hpB n
  exact hp p.2 hpB n

/-- On rooted continuity sets, the normalized LQG masses are limits in
measure of functions of the original canonical field and the sampled root. -/
theorem IsWholePlaneGFF.exists_canonical_unitBall_rooted_mass_approximations
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ ε : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {ν : Ω → Measure ℂ}
    (hh : IsWholePlaneGFF P hC hcirc) (hν : IsLQGMeasureOfField P γ α₀ hcirc ν)
    (H : Ω → LQGMetric.DistC) (hH : Measurable H)
    (hversion : ∀ φ : LQGMetric.TestC0,
      (fun ω => H ω φ.1) =ᵐ[P] (fun ω => hC ω φ.1))
    (hmass : ∀ᵐ ω ∂P, ν ω (ball 0 1) ≠ 0) (hε : 0 < ε)
    (E : ℕ → Set ℂ) (hEm : ∀ n, MeasurableSet (E n)) (hmono : Monotone E)
    (hunion : (⋃ n, E n) = ball 0 ε)
    (S : Set (Set ℂ)) (hsets : ∀ A ∈ S, MeasurableSet A)
    (hfront : ∀ A ∈ S, ∀ᵐ x ∂(P ⊗ₘ weightedRestrictionKernel P ν
      (hh.aemeasurable_lqgMeasure hν) (ball 0 1) measurableSet_ball
      (fun _ => 1) measurable_const),
      let η := (ν x.1).map (fun v : ℂ => v - x.2)
      (∀ n, η (frontier (E n)) = 0 ∧ η (frontier (A ∩ E n)) = 0) ∧
        η (frontier (⋃ n, E n)) = 0 ∧ η (frontier (A ∩ ⋃ n, E n)) = 0) :
    ∃ f : S → ℕ → LQGMetric.DistC × ℂ → ℝ,
      (∀ A n, Measurable (f A n)) ∧ ∀ A, TendstoInMeasure
        (P ⊗ₘ weightedRestrictionKernel P ν (hh.aemeasurable_lqgMeasure hν)
          (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const)
        (fun n x => f A n (H x.1, x.2)) atTop
        (fun x => (normalizedRestriction
          ((ν x.1).map (fun v : ℂ => v - x.2)) (ball 0 ε) A.val).toReal) := by
  let : IsProbabilityMeasure P := hh.isProbabilityMeasure
  let hm := hh.aemeasurable_lqgMeasure hν
  let K := weightedRestrictionKernel P ν hm (ball 0 1) measurableSet_ball
    (fun _ => 1) measurable_const
  have hsub : ∀ n, E n ⊆ ball 0 ε := by
    intro n
    rw [← hunion]
    exact subset_iUnion E n
  obtain ⟨F, hFm, hFeq⟩ := hh.exists_sampled_canonical_normalizedLQGApprox
    (γ := γ) (α₀ := α₀) H hversion K (ball 0 1)
    (ae_mem_weightedRestriction_compProd P ν hm (ball 0 1) measurableSet_ball
      (fun _ => 1) measurable_const) E hEm (unitBall_rooted_dyadic_buffer hε E hsub)
  have hX : Measurable (fun x : Ω × ℂ => (H x.1, x.2)) :=
    (hH.comp measurable_fst).prodMk measurable_snd
  have hmass' : ∀ᵐ ω ∂P, ((ν ω).withDensity (fun _ => 1)) (ball 0 1) ≠ 0 ∧
      ((ν ω).withDensity (fun _ => 1)) (ball 0 1) ≠ ∞ := by
    filter_upwards [hmass, hν] with ω hω hνω
    let : IsLocallyFiniteMeasure (ν ω) := hνω.isLocallyFiniteMeasure
    simp only [withDensity_const, one_smul]
    exact ⟨hω, measure_ball_ne_top⟩
  have hc : ∀ᵐ ω ∂P, ∀ n,
      Continuous (fieldCircleAverage α₀ (hcirc ω) (dyadicScale n)) :=
    ae_all_iff.mpr fun n => hh.ae_continuous_fieldCircleAverage α₀ (dyadicScale_pos n)
  refine ⟨fun A n p => (F n p A.val).toReal, ?_, ?_⟩
  · intro A n
    exact ENNReal.measurable_toReal.comp ((Measure.measurable_coe (hsets A A.property)).comp (hFm n))
  · exact tendstoInMeasure_rooted_normalizedMass_of_approximation P
      (fun ω => fieldCircleAverage α₀ (hcirc ω)) ν hm hν hc
      (ball 0 1) measurableSet_ball (fun _ => 1) measurable_const hmass' hε E hmono hunion
      S hsets hfront _ hX F hFm hFeq

#print axioms IsWholePlaneGFF.exists_canonical_rooted_normalizedLQGApprox
#print axioms IsWholePlaneGFF.exists_sampled_canonical_normalizedLQGApprox
#print axioms IsWholePlaneGFF.exists_canonical_unitBall_rooted_mass_approximations

end HarmonicBalls
