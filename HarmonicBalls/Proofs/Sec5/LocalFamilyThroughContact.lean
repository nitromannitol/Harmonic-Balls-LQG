import HarmonicBalls.Proofs.Sec5.LocalFirstContactRepresentative

/-! # Field-local regularized family through first contact -/

namespace HarmonicBalls

open MeasureTheory Metric Set Filter
open scoped ENNReal Topology

universe u

/-- Any exact containment horizon admits a field-local representative of the
regularized family at every positive time up to and including the horizon.
The locality input is proposed and awaits source review. -/
theorem exists_fieldLocal_regularizedFamily_through_horizon
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z)
    (H : Ω → U → ℝ≥0∞)
    (hchar : ∀ᵐ ω ∂P, ∀ z : U, ∀ t : ℝ, 0 < t →
      (ENNReal.ofReal t < H ω z ↔ closure (Λ ω z t) ⊆ U)) :
    ∃ F : Ω → (U × Ioi (0 : ℝ) → Set ℂ),
      Measurable[fieldSigmaAlgebra α₀ hC U] F ∧
      ∀ᵐ ω ∂P,
        (∀ p : U × Ioi (0 : ℝ), ENNReal.ofReal p.2 ≤ H ω p.1 →
          F ω p = Λ ω p.1 p.2) ∧
        (∀ (z : U) (t s : Ioi (0 : ℝ)), H ω z ≤ ENNReal.ofReal t →
          H ω z ≤ ENNReal.ofReal s → F ω (z, t) = F ω (z, s)) := by
  classical
  obtain ⟨E, G, hE, hG, heq⟩ := exists_local_lqg_open_stoppedFamily_representative
    hI2 hγ hγ2 hα hGFF hμ hloc hU hΛ
  let Q := {q : ℚ // 0 < (q : ℝ)}
  let A : Ω → (U × Ioi (0 : ℝ)) → Set ℂ := fun ω p =>
    {x | ∃ q : Q, (q : ℝ) < p.2 ∧ E ω (p.1, ⟨q, q.property⟩) ∧
      x ∈ G ω (p.1, ⟨q, q.property⟩)}
  have hA : Measurable[fieldSigmaAlgebra α₀ hC U] A := by
    let : MeasurableSpace Ω := fieldSigmaAlgebra α₀ hC U
    apply Measurable.of_eval
    intro p
    apply Measurable.of_eval
    intro x
    change Measurable (fun ω => ∃ q : Q, (q : ℝ) < p.2 ∧
      E ω (p.1, ⟨q, q.property⟩) ∧ x ∈ G ω (p.1, ⟨q, q.property⟩))
    apply Measurable.exists
    intro q
    exact measurable_const.and (((measurable_pi_apply (p.1, (⟨(q : ℚ), q.property⟩ : Ioi (0 : ℝ)))).comp hE).and
      ((measurable_pi_apply x).comp
        ((measurable_pi_apply (p.1, (⟨(q : ℚ), q.property⟩ : Ioi (0 : ℝ)))).comp hG)))
  have hAstop : ∀ᵐ ω ∂P, ∀ (z : U) (t s : Ioi (0 : ℝ)),
      H ω z ≤ ENNReal.ofReal t → H ω z ≤ ENNReal.ofReal s →
      A ω (z, t) = A ω (z, s) := by
    filter_upwards [heq, hchar] with ω heqω hcharω
    intro z t s ht hs
    ext x
    change (∃ q : Q, (q : ℝ) < t ∧ E ω (z, ⟨q, q.property⟩) ∧
      x ∈ G ω (z, ⟨q, q.property⟩)) ↔
      (∃ q : Q, (q : ℝ) < s ∧ E ω (z, ⟨q, q.property⟩) ∧
      x ∈ G ω (z, ⟨q, q.property⟩))
    have hbefore (q : Q) (hq : E ω (z, ⟨q, q.property⟩)) :
        ENNReal.ofReal (q : ℝ) < H ω z :=
      (hcharω z q q.property).mpr ((heqω _).1.mp hq)
    constructor
    · rintro ⟨q, _, hq, hx⟩
      exact ⟨q, (ENNReal.ofReal_lt_ofReal_iff s.property).mp
        (lt_of_lt_of_le (hbefore q hq) hs), hq, hx⟩
    · rintro ⟨q, _, hq, hx⟩
      exact ⟨q, (ENNReal.ofReal_lt_ofReal_iff t.property).mp
        (lt_of_lt_of_le (hbefore q hq) ht), hq, hx⟩
  refine ⟨(fun ω p => denseSequenceRegularization (A ω p)),
    measurable_denseSequenceRegularization_family.comp hA, ?_⟩
  filter_upwards [heq, hΛ, hchar, hAstop] with ω heqω hΛω hcharω hAstopω
  constructor
  swap
  · intro z t s ht hs
    exact congrArg denseSequenceRegularization (hAstopω z t s ht hs)
  intro p hle
  let B := ⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ (q : ℝ) < p.2}, Λ ω p.1 q
  have hBopen : IsOpen B := isOpen_iUnion fun q =>
    ((hΛω p.1).1.isRegularOpen q q.property.1).isOpen
  have hgood (q : Q) (hqt : (q : ℝ) < p.2) : E ω (p.1, ⟨q, q.property⟩) := by
    apply (heqω _).1.mpr
    apply (hcharω p.1 q q.property).mp
    exact lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff p.2.property).mpr hqt) hle
  have hAB : A ω p = B := by
    ext x
    change (∃ q : Q, (q : ℝ) < p.2 ∧ E ω (p.1, ⟨q, q.property⟩) ∧
      x ∈ G ω (p.1, ⟨q, q.property⟩)) ↔ x ∈ B
    simp only [B, mem_iUnion]
    constructor
    · rintro ⟨q, hqt, hq, hx⟩
      exact ⟨⟨q, q.property, hqt⟩, (heqω _).2.1 hq ▸ hx⟩
    · rintro ⟨q, hx⟩
      let q' : Q := ⟨q, q.property.1⟩
      have hq := hgood q' q.property.2
      exact ⟨q', q.property.2, hq, (heqω _).2.1 hq ▸ hx⟩
  have hcl := closure_eq_closure_iUnion_earlier_rat_of_hausdorffContinuousOn p.2.property
    (fun s hs t ht hst => (hΛω p.1).1.monotoneOn hs ht hst)
    (hΛω p.1).1.hausdorffContinuousOn
  rw [hAB, denseSequenceRegularization_eq hBopen, ← hcl,
    (hΛω p.1).1.isRegularOpen _ p.2.property]

/-- On an arbitrary open domain, a field-local horizon and a field-local
regularized family agree with the given family through that horizon, including
first contact whenever it is positive and finite. -/
theorem exists_fieldLocal_open_family_through_contact
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ H : Ω → (U → ℝ≥0∞), ∃ F : Ω → (U × Ioi (0 : ℝ) → Set ℂ),
      Measurable[fieldSigmaAlgebra α₀ hC U] H ∧
      Measurable[fieldSigmaAlgebra α₀ hC U] F ∧
      ∀ᵐ ω ∂P, ∀ z : U,
        (∀ t : ℝ, 0 < t →
          (ENNReal.ofReal t < H ω z ↔ closure (Λ ω z t) ⊆ U)) ∧
        (∀ t : Ioi (0 : ℝ), ENNReal.ofReal t ≤ H ω z → F ω (z, t) = Λ ω z t) ∧
        (∀ t s : Ioi (0 : ℝ), H ω z ≤ ENNReal.ofReal t →
          H ω z ≤ ENNReal.ofReal s → F ω (z, t) = F ω (z, s)) ∧
        (0 < H ω z → H ω z < ⊤ →
          (closure (Λ ω z (H ω z).toReal) ∩ frontier U).Nonempty) := by
  obtain ⟨H, hH, hchar⟩ := exists_fieldLocal_open_horizons_with_conditional_boundary_contact
    hI2 hγ hγ2 hα hGFF hμ hloc hU hΛ
  have hchar' : ∀ᵐ ω ∂P, ∀ z : U, ∀ t : ℝ, 0 < t →
      (ENNReal.ofReal t < H ω z ↔ closure (Λ ω z t) ⊆ U) := by
    filter_upwards [hchar] with ω hω
    exact fun z => (hω z).1
  obtain ⟨F, hF, hFeq⟩ := exists_fieldLocal_regularizedFamily_through_horizon
    hI2 hγ hγ2 hα hGFF hμ hloc hU hΛ H hchar'
  refine ⟨H, F, hH, hF, ?_⟩
  filter_upwards [hchar, hFeq] with ω hcharω hFeqω
  exact fun z => ⟨(hcharω z).1, (fun t ht => hFeqω.1 (z, t) ht),
    (fun t s ht hs => hFeqω.2 z t s ht hs), (hcharω z).2⟩

/-- For a bounded open domain, the field determines the whole regularized
family through its positive finite first-contact time, simultaneously for all
centres. The locality, affine invariance and coordinate change inputs are
proposed and await source review. -/
theorem exists_fieldLocal_bounded_open_family_through_contact
    {Ω : Type u} [MeasurableSpace Ω] {P : Measure Ω} {γ α₀ : ℝ}
    {hC : Ω → (ℂ → ℝ) → ℝ} {hcirc : Ω → ℝ → ℂ → ℝ} {μ : Ω → Measure ℂ}
    (hI2 : LQGVolumeGrowthAllScalesStmt.{u})
    (h71 : ClusterUpperBoundPolyHighProbStmt.{u})
    (hAff : WholePlaneGFFAffineInvariance P hC hcirc)
    (hCC : LQGMeasureCoordChange P γ α₀ hC hcirc)
    (hγ : 0 < γ) (hγ2 : γ < 2) (hα : α₀ < lqgQ γ)
    (hGFF : IsWholePlaneGFF P hC hcirc) (hμ : IsLQGMeasureOfField P γ α₀ hcirc μ)
    (hloc : LQGMeasureLocality P γ α₀ hC hcirc)
    {U : Set ℂ} (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    {Λ : Ω → ℂ → ℝ → Set ℂ}
    (hΛ : ∀ᵐ ω ∂P, ∀ z, IsRegularizedClusterFamily (μ ω) (Λ ω z) z) :
    ∃ H : Ω → (U → ℝ≥0∞), ∃ F : Ω → (U × Ioi (0 : ℝ) → Set ℂ),
      Measurable[fieldSigmaAlgebra α₀ hC U] H ∧
      Measurable[fieldSigmaAlgebra α₀ hC U] F ∧
      ∀ᵐ ω ∂P, ∀ z : U, 0 < H ω z ∧ H ω z ≤ μ ω U ∧ H ω z < ⊤ ∧
        (∀ t : ℝ, 0 < t →
          (ENNReal.ofReal t < H ω z ↔ closure (Λ ω z t) ⊆ U)) ∧
        (∀ t : Ioi (0 : ℝ), ENNReal.ofReal t ≤ H ω z → F ω (z, t) = Λ ω z t) ∧
        (∀ t s : Ioi (0 : ℝ), H ω z ≤ ENNReal.ofReal t →
          H ω z ≤ ENNReal.ofReal s → F ω (z, t) = F ω (z, s)) ∧
        (closure (Λ ω z (H ω z).toReal) ∩ frontier U).Nonempty := by
  obtain ⟨H, hH, hchar⟩ := exists_fieldLocal_bounded_open_horizons_positive
    hI2 h71 hAff hCC hγ hγ2 hα hGFF hμ hloc hU hUb hΛ
  have hchar' : ∀ᵐ ω ∂P, ∀ z : U, ∀ t : ℝ, 0 < t →
      (ENNReal.ofReal t < H ω z ↔ closure (Λ ω z t) ⊆ U) := by
    filter_upwards [hchar] with ω hω
    exact fun z => (hω z).2.2.2.1
  obtain ⟨F, hF, hFeq⟩ := exists_fieldLocal_regularizedFamily_through_horizon
    hI2 hγ hγ2 hα hGFF hμ hloc hU hΛ H hchar'
  refine ⟨H, F, hH, hF, ?_⟩
  filter_upwards [hchar, hFeq] with ω hcharω hFeqω
  intro z
  exact ⟨(hcharω z).1, (hcharω z).2.1, (hcharω z).2.2.1,
    (hcharω z).2.2.2.1, (fun t ht => hFeqω.1 (z, t) ht),
    (fun t s ht hs => hFeqω.2 z t s ht hs), (hcharω z).2.2.2.2⟩

#print axioms exists_fieldLocal_regularizedFamily_through_horizon
#print axioms exists_fieldLocal_open_family_through_contact
#print axioms exists_fieldLocal_bounded_open_family_through_contact

end HarmonicBalls
